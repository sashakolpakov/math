import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PreservingUnits
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.IsomorphismUniqueness

/-! # Unit Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The unit associated to a polarized level-preserving automorphism determines the entire isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable {A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S}

theorem Moduli.Isomorphisms.LevelPreservingIso.levelUnit_injective : Function.Injective (Moduli.Isomorphisms.LevelPreservingIso.levelUnit (A := A)) := by
  intro e f h
  apply Moduli.Isomorphisms.LevelPreservingIso.ext_abelian
  exact congrArg (fun v : A.abelian.levelUnitSubgroup N => v.val.val.toMul.hom.hom) h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
