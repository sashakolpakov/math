import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.IsomorphismUniqueness
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Isomorphism Pullback Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Faithful scheme base change detects actual polarized full-level isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable {A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S}

theorem Moduli.Isomorphisms.LevelPreservingIso.pullback_injective (f : T ⟶ S) [(Over.pullback f).Faithful] :
    Function.Injective (fun e : Moduli.Isomorphisms.LevelPreservingIso A B => e.pullback f) := by
  intro e d h
  apply Moduli.Isomorphisms.LevelPreservingIso.ext_abelian e d
  apply (Over.pullback f).map_injective
  exact congrArg (fun z : Moduli.Isomorphisms.LevelPreservingIso (A.pullback f) (B.pullback f) => z.abelian.hom) h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
