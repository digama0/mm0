// Keeping the open file in the browser, so a refresh does not need it again.
//
// IndexedDB rather than localStorage: localStorage holds strings, so bytes have
// to go through base64 (+33%) against a ~5MB quota -- hello_mmc is 3.5MB, which
// becomes 4.7MB of string and lands right on the limit -- and the write is
// synchronous, so it would block the main thread on every open. IndexedDB
// stores an ArrayBuffer as it is, asynchronously, with room to spare.
//
// Nothing leaves the machine either way. This is the same tab's storage, under
// the same origin.

const DB = 'mm0-js';
const STORE = 'files';
const KEY = 'last';

/** Files above this are not kept: the point is convenience, not archival. */
const MAX_BYTES = 64 * 1024 * 1024;

export interface Saved {
  name: string;
  bytes: ArrayBuffer;
}

function open(): Promise<IDBDatabase> {
  return new Promise((resolve, reject) => {
    const req = indexedDB.open(DB, 1);
    req.onupgradeneeded = () => {
      if (!req.result.objectStoreNames.contains(STORE)) req.result.createObjectStore(STORE);
    };
    req.onsuccess = () => resolve(req.result);
    req.onerror = () => reject(req.error ?? new Error('indexedDB open failed'));
  });
}

function run<T>(mode: IDBTransactionMode, fn: (s: IDBObjectStore) => IDBRequest<T>): Promise<T> {
  return open().then((db) => new Promise<T>((resolve, reject) => {
    const tx = db.transaction(STORE, mode);
    const req = fn(tx.objectStore(STORE));
    req.onsuccess = () => resolve(req.result);
    req.onerror = () => reject(req.error ?? new Error('indexedDB request failed'));
    tx.oncomplete = () => db.close();
  }));
}

/**
 * Keep this file for next time. Failures are swallowed: storage can be
 * disabled, full, or refused in a private window, and none of that should stop
 * the file being read.
 */
export async function save(name: string, bytes: Uint8Array): Promise<void> {
  if (bytes.byteLength > MAX_BYTES) return;
  try {
    // A copy, because the caller's view may be over a larger buffer and
    // structured clone would store all of it.
    const buf = bytes.slice().buffer;
    await run('readwrite', (s) => s.put({ name, bytes: buf } satisfies Saved, KEY));
  } catch {
    // Convenience only.
  }
}

/** The file kept last time, if any. */
export async function load(): Promise<Saved | null> {
  try {
    const v = await run<Saved | undefined>('readonly', (s) => s.get(KEY));
    return v === undefined ? null : v;
  } catch {
    return null;
  }
}

/** Forget it, for the button that says so. */
export async function clear(): Promise<void> {
  try {
    await run('readwrite', (s) => s.delete(KEY));
  } catch {
    // Nothing to do if storage is unavailable.
  }
}
