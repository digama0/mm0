// Verifying a whole file.
//
// The statement loop of mm0-c/verifier.c's `verify`: walk the declaration
// stream in order, check each declaration's own table entry, run its proof,
// and check the result against its header.
//
// What this adds over running the machine on a declaration in isolation is
// *order*. Ids are assigned in stream order, and a proof may only name what
// has already been declared, so the running counts are passed down as limits.
// Without that a definition could refer to itself or to a later one, and the
// redundancy that rules out cyclic definitions -- the proof stream building a
// value that the unify stream must then match -- would rule out nothing.

import { CLASS, MmbError, type Decl, type MmbFile } from './mmb.js';
import { Machine, MachineError, type Limits, type Where } from './machine.js';
import { nameRef } from './msg.js';

export interface Failure {
  /** Position in the declaration stream. */
  index: number;
  /** `sort`/`term`/`def`/... and the declaration's name. */
  what: string;
  /**
   * Where inside the declaration it failed, outermost first: `step 12`,
   * `unify step 3`, `arg 2`. Empty when the declaration itself is at fault
   * rather than a part of it.
   */
  where: Where[];
  message: string;
}

export interface Report {
  ok: boolean;
  failures: Failure[];
  /**
   * Declarations that verified.
   *
   * All of them, not only the ones with a proof stream. A sort is verified as
   * much as a theorem is -- its id is checked against the table and it may not
   * overflow the declared count -- and a plain term has its sort, purity and
   * return type checked. There is simply nothing to *run* for either. Counting
   * only the streams reported fewer verified declarations than the file has,
   * which reads as a discrepancy rather than as the distinction it is.
   */
  verified: number;
  /**
   * Whether a declaration hit the per-declaration cap, so `failures` is a
   * floor rather than a total -- there are at least this many.
   */
  capped: boolean;
  /**
   * Declarations that used `Sorry`. With the index, not just the label: it is
   * a declaration like any other, and a report naming one should be able to
   * say where it is.
   */
  sorried: { index: number; what: string }[];
  proofSteps: number;
  unifySteps: number;
}

/**
 * Verify every declaration of a file, in order.
 *
 * Collects failures rather than stopping at the first, so a broken file
 * reports everything wrong with it -- the debugging case cares about that far
 * more than about a single message. `ok` is true only if nothing failed and
 * nothing used `Sorry`.
 */
export function verify(file: MmbFile): Report {
  const failures: Failure[] = [];
  const sorried: { index: number; what: string }[] = [];
  let verified = 0, proofSteps = 0, unifySteps = 0;
  let capped = false;
  // The running counts: what has been declared so far, which is what a proof
  // is allowed to name.
  const limits: Limits = { sorts: 0, terms: 0, thms: 0 };
  /** Where the declaration stream ended, however it ended. */
  let stopped: number | undefined;

  const name = (d: Decl): string =>
    d.cls === CLASS.SORT ? file.sortName(d.num)
      : d.cls === CLASS.TERM ? file.termName(d.num) : file.thmName(d.num);

  // The declaration walk can itself fail -- a bad statement length, a truncated
  // stream -- and that is a verdict, not an exception. Driving the generator by
  // hand keeps those inside the report like every other failure, so `verify`
  // is total for any input.
  const decls = file.decls();
  for (;;) {
    let step: IteratorResult<Decl, number>;
    try {
      step = decls.next();
    } catch (e) {
      if (!(e instanceof MmbError)) throw e;
      failures.push({
        index: -1, what: 'declaration stream',
        where: e.pos === undefined ? [] : [{ at: 'byte', offset: e.pos }],
        message: e.message,
      });
      // The walk did not reach an `END`; where it gave up is where it stopped.
      stopped = e.pos;
      break;
    }
    if (step.done === true) { stopped = step.value; break; }
    const d = step.value;
    const what = `${['sort', 'term', 'theorem'][d.cls]} ${name(d)}`;
    let at = -1;
    // Failures the machine carried on past are collected as they appear, so
    // each is tagged with the step it happened at rather than all of them with
    // the step the declaration finally gave up on.
    let seen = 0;
    let m: Machine | null = null;
    const drain = (): void => {
      if (m === null) return;
      for (const e of m.errors.slice(seen)) {
        const w = at < 0 ? e : e.under({ at: 'step', index: at });
        failures.push({ index: d.index, what, where: w.where, message: w.message });
      }
      seen = m.errors.length;
    };
    try {
      // `Sort` and `Term` have no proof stream: their `data` is the length of
      // the statement's own command, so the next command is the next
      // statement. mm0-c checks this as `data == sz`; without it a `term` can
      // carry a whole proof stream, which is then run and accepted -- bytes
      // the format says are not there, verified as if they were.
      if (d.cls === CLASS.SORT || (d.cls === CLASS.TERM && !d.isDef)) {
        if (!d.proof.isNull) {
          throw new MachineError(
            `a ${d.cls === CLASS.SORT ? 'sort' : 'term'} has no proof stream,`
            + ' but this statement is followed by one');
        }
      }
      if (d.cls === CLASS.SORT) {
        if (limits.sorts >= file.numSorts)
          throw new MachineError('more sorts declared than the header allows');
        limits.sorts++;
        verified++;
        continue;
      }
      if (d.cls === CLASS.TERM) {
        if (limits.terms >= file.numTerms)
          throw new MachineError('more terms declared than the header allows');
        const td = file.term(d.num);
        // The term's own sort field, which is not the same thing as the return
        // type's -- they are checked against each other below, and a file can
        // have one right and the other wrong. Saying which is which matters:
        // the view renders the *return* type, so a declaration whose sort
        // field is wrong still renders correctly.
        if (td.sort >= limits.sorts) {
          throw new MachineError(`td.sort ${td.sort} is not a declared sort`
            + ` (${limits.sorts} so far)`);
        }
        // A pure sort has no terms at all: it is inhabited only by variables.
        if (file.sortIsPure(td.sort)) {
          throw new MachineError(
            `td.sort is ${nameRef('sort', file.sortName(td.sort))}, a pure sort`);
        }
        if (td.ret.sort !== td.sort) {
          throw new MachineError(`ret.sort ${td.ret.sort} does not match td.sort`
            + ` ${td.sort}`);
        }
        // mm0-c compares the whole upper byte -- `(ret >> 56) == sort`
        // (verifier.c) -- which is the sort *and* the bound bit above it. A
        // return type is never bound, so the bit must be clear; checking only
        // the sort would accept a file mm0-c rejects.
        if (td.ret.bound) {
          throw new MachineError('the return type is marked bound');
        }
      } else {
        if (limits.thms >= file.numThms)
          throw new MachineError('more theorems declared than the header allows');
      }

      m = new Machine(file, d, limits);
      const it = d.proof;
      // Which command of the proof is running, so a failure can name it. Read
      // in the catch below rather than wrapped per iteration: the loop leaves
      // it on the command that threw, and a try/catch around 244,778 of them
      // would be paid for by every file that verifies.
      if (!it.isNull) {
        while (it.step()) {
          at++;
          proofSteps++;
          m.apply(it.cmd, it.data);
          if (m.errors.length > seen) drain();
        }
        if (it.error) throw new MachineError(it.error.message, [{ at: 'step', index: at + 1 }]);
      }
      // Past the stream: what follows belongs to the declaration, not a step.
      at = -1;
      m.endCheck(d);
      drain();
      unifySteps += m.unifySteps;
      // A declaration the machine carried on through is still not verified.
      if (m.errors.length === 0) verified++;
      if (m.usesSorry) sorried.push({ index: d.index, what });
    } catch (e) {
      // A declaration can fail in two ways, and both are verdicts about it.
      // A `MachineError` is a proof that does not check. An `MmbError` is the
      // declaration's own table entry being unreadable -- a `p_args` that
      // points outside the file, an argument count that runs off the end --
      // which surfaces here because the machine reads the entry as it starts.
      //
      // Only the first used to be caught, so the second escaped `verify`
      // entirely and took the whole file with it: every other declaration had
      // already been walked and listed, and one bad pointer left the reader
      // with the unreadable-file screen instead of a list with one bad row.
      // That is the outcome this function exists to avoid.
      if (!(e instanceof MachineError) && !(e instanceof MmbError)) throw e;
      // Whatever it carried on past comes first: those are the failures, and
      // this one is where it stopped.
      drain();
      if (e instanceof MmbError) {
        failures.push({
          index: d.index, what,
          // Its position is a byte, not a step: the entry was never read, so
          // there is no step to point at.
          where: e.pos === undefined ? [] : [{ at: 'byte', offset: e.pos }],
          message: e.message,
        });
      } else {
        const err = at < 0 ? e : e.under({ at: 'step', index: at });
        // Giving up is not a defect of the file, it is a limit of this report:
        // the failures it stopped after are already listed, and what the reader
        // needs to know is that there may be more. `capped` says so; a line
        // saying it as well would be counted among the things to fix.
        if (m?.gaveUp === true) capped = true;
        else failures.push({ index: d.index, what, where: err.where, message: err.message });
      }
    }
    // Counted after the checks, so a failed declaration does not become
    // referenceable by the ones that follow. A sort is counted on its success
    // path and nowhere else: a failed one reaching here must raise no budget at
    // all, or it would raise the *theorem* budget and let a later proof apply a
    // theorem that has not been checked yet -- the forward reference this
    // counting exists to prevent.
    if (d.cls === CLASS.TERM) limits.terms++;
    else if (d.cls === CLASS.THM) limits.thms++;
  }

  // Every table entry must have been claimed by a declaration. A file with
  // more terms in its table than in its stream would leave the surplus
  // unchecked while still being referenceable by name.
  // One failure, not three: a stream that stops early is short of everything
  // after the point it stopped, so three lines saying so are three views of the
  // same fact. The counts are what a reader wants -- how far it got.
  const short: string[] = [];
  if (limits.sorts !== file.numSorts) short.push(`${limits.sorts}/${file.numSorts} sorts`);
  if (limits.terms !== file.numTerms) short.push(`${limits.terms}/${file.numTerms} terms`);
  if (limits.thms !== file.numThms) short.push(`${limits.thms}/${file.numThms} theorems`);
  if (short.length > 0) {
    // The stream is what fell short, and where it ended is the fact worth
    // having -- so it is attributed like any other stream failure, and says
    // `declaration stream` once, on the trail, rather than twice.
    failures.push({
      index: -1, what: 'declaration stream',
      where: stopped === undefined ? [] : [{ at: 'byte', offset: stopped }],
      message: `incomplete (${short.join(', ')})`,
    });
  }

  return {
    ok: failures.length === 0 && sorried.length === 0,
    failures, capped, verified, sorried, proofSteps, unifySteps,
  };
}
