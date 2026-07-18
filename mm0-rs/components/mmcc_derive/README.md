# mmcc_derive

Derive macros for the [`mmcc`](../mmcc) binary encoding: `Encode` and `Decode`, which
write a value into the format described in `mmcc::encode`.

The generated code is the field-by-field walk and nothing else. Everything shared across
types — the encoding context, which types are interned — is declared by the `interned!`
macro in `mmcc::encode`, since a derive sees one type at a time.
