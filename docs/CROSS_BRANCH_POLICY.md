# Research inputs and cross-branch sources

The repository `randogelist/zetahyperbolic-axiom` is the source-level home of the Leaned Paper. Its existing 52-page PDF remains the canonical manuscript.

* **Compiled upstream basis:** `randogelist/snditeration@ef9beea7cb3f58a4047aed7e5a2974dfb94fba30`, including Mathlib 4.33 Section 2 algebra and audit.
* **Additional research sources:** `randogelist/BATCH-ONE`, `randogelist/zetazeven`, `randogelist/zeta_Zeven`, `randogelist/zeta7-777`, and IRRATIONALITY ZIPs. These require source provenance and exact theorem checks before importing.
* **Research permitted:** mathematical conjectures, rough derivations and independently sourced proof strategies may accelerate development, but stay outside the certified theorem import graph until proved.
* **Native LEAN_ANCHORINGS:** preload compatible Mathlib, then verified immutable Lean anchors; compile changed/invalidated modules only, with source + olean + dependency + toolchain fingerprint.
* **Workflow modes:** B_TIER_DERIVATION, A_TIER_PLANNING and A_TIER_EXECUTION. Neither modes nor package suffixes promote theorem status.

Next manuscript-chronological target: full Lemma 2.2 and Lemma 2.3, then the analytic Gram realization enabling Theorem 3.1.
