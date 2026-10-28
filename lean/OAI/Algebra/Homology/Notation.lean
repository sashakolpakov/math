import Mathlib.Algebra.Homology.ComplexShape

/-! # Notation -/

namespace OAI.Algebra.Homology.Notation

/-!
# Notation for the cohomological complex shape

`ℤᵘᵖ` denotes the cohomological complex shape on the integers, whose differentials increase
degree by one.
-/

/-- `ℤᵘᵖ` is `ComplexShape.up ℤ`, the cohomological complex shape on integer degrees: its
potentially nonzero differentials have type `K.X n ⟶ K.X (n + 1)`. -/
notation "ℤᵘᵖ" => ComplexShape.up Int

end OAI.Algebra.Homology.Notation
