# Verification report

Verified on 23 October 2026 with Lean 4.32.0 and the checked-in exact Lake
manifest. Run `make verify` from this directory to repeat the checks.

* The complete target, including all 12 project Lean files, compiled.
* The project-source scan found no unfinished proofs, project axioms or
  native-decision shortcuts.
* All 17 public declaration audits compiled and reported only `propext`,
  `Classical.choice` and `Quot.sound`.
* The new `provedOptimizedDeficitArithmetic` theorem and its knot-count
  consequence passed the same kernel/axiom checks as the original target.
* The new upper-coefficient theorem passed those checks as well.

The certificate is conditional on the typed external inputs listed in
[MANUSCRIPT_MAP.md](MANUSCRIPT_MAP.md). Standard axiom dependencies do not
prove these theorem parameters. The classical knot quotient and auxiliary
link construction remain outside the formal target.

The corpus release manifest records the exact candidate source hashes,
including this report; dependency caches and raw compiler logs are omitted
from the contribution.
