import OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothProperModel
import OAI.ArithmeticGeometry.Models.SpreadingOut.SpreadFiniteDiagram

/-! # Core -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.Core

/-!
# SpreadingOut: smooth proper models outside finitely many primes

Both conclusions of the frozen `Statements/SpreadingOut.lean` specification are proved
in `Hodge.SpreadingOutProof`:

* `smooth_proper_model_outside_finitely_many_primes` gives a smooth proper
 model over a cofinite arithmetic open without extending the number field.
* `spread_finite_diagram_with_abelian_varieties` gives simultaneous models
 after a finite number-field extension, split geometric components,
 compatible arrows, and the prescribed commutative group structures with
 geometrically connected fibers and group-compatible generic isomorphisms.

The arithmetic-base and finite-extension structures reproduce the frozen
specification. No statement stubs are imported. The geometric-fiber argument
uses absolute irreducibility, generic flatness over Dedekind domains, and
fiberwise density of suitable principal opens.
-/

end OAI.ArithmeticGeometry.Models.SpreadingOut.Core
