# R(5,5) — recovered circulant order census

**Author:** Jared Wilder  
**Recovered from:** release-day archive seam, 2026-09-11

The archive seam recovered an exact computational census surrounding the 41-vertex circulant program.

Within the family of inverse-closed Cayley graphs on cyclic groups tested by the source campaign:

- order `39`: **no** circulant `(5,5)` Ramsey witness;
- order `40`: a circulant witness exists;
- order `41`: the classified witness family exists, with the unique multiplier/affine class described in this directory;
- order `42`: **no** circulant `(5,5)` Ramsey witness.

For `n=42`, the source reports exhaustive traversal of all

\[
2^{21}-1=2,097,151
\]

nonempty inverse-closed connection sets, with zero survivors.

Thus existence inside the circulant family is **not monotone in the order**: witnesses occur at 40 and 41 while none occur at 39 or 42.

This is a classification inside a restricted construction family. It is not a global statement about all graphs on 42 vertices and therefore does not determine `R(5,5)`.

The original exhaustive-search implementation should be routed into the eventual dedicated R(5,5) structural repository so the `2,097,151`-case result is reproducible from the canonical home rather than only recoverable from the archive seam.
