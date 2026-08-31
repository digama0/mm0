// Naming a declaration inside a failure message.
//
// A message that mentions a declaration is usually read in order to go and look
// at it, so the name wants to be a link. It cannot be recovered from the text:
// sorts, terms and theorems are separate namespaces, so `T` may be a term and a
// theorem at once, and a reader guessing from the spelling alone picks one of
// them and is silently wrong whenever it guesses the other.
//
// So the namespace is written down where the message is built, which is the
// only place that knows it. The marker is still backticks, which is what these
// messages already used to set a name apart.

/** Which namespace a name is in. Matches `CLASS`, spelled for a reader. */
export type NameKind = 'sort' | 'term' | 'thm';

/** A declaration named in a message: `` `term:T` ``. */
export const nameRef = (kind: NameKind, name: string): string => `\`${kind}:${name}\``;

/** Splits a message into its literal text and the names it refers to. */
export const REF = /`(sort|term|thm):([^`]*)`/g;

/**
 * An argument of the declaration a step applies: `` `arg:3:G` ``.
 *
 * The position and the binder's name, and nothing else. What that argument was
 * substituted with is not written down: it is on the stack at that step, so
 * anything replaying the proof can reconstruct it, and a message carrying a
 * copy would be carrying state that can go stale or be redrawn against the
 * wrong arena. The name travels because it is a fact about the declaration
 * rather than about the run, and a reader without the replay still needs it.
 */
export const argRef = (i: number, name: string): string => `\`arg:${i}:${name}\``;

/** Splits out an argument reference: its position, then its name. */
export const ARG = /`arg:(\d+):([^`]*)`/g;

/**
 * The message as plain text, for anywhere that cannot carry a link or does not
 * have the arena. The markers are an encoding, not something to read.
 */
export const plainMessage = (text: string): string =>
  text.replace(REF, (_, _kind: string, name: string) => name)
    .replace(ARG, (_, _i: string, name: string) => name);
