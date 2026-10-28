import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReductionOpens

/-! # Equal Reduction Open Squares -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EqualReductionOpenSquares

noncomputable section

/-! Maps out of the actual dual-number product with the same
reduction have identical underlying points and inverse-image opens.
Their restrictions to each common open square are constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {Y : Scheme.{0}}
    (f g : (LieRanks.dualNumberTest ℂ ⊗ X).left ⟶ Y)
    (h : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ f = (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ g)

include h in
theorem equalDualReduction_point (x : (LieRanks.dualNumberTest ℂ ⊗ X).left) : f x = g x := by
  obtain ⟨y, rfl⟩ := (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction_surjective X).surj x
  exact congrArg (fun a : X.left ⟶ Y => a y) h

include h in
theorem equalDualReduction_preimage (U : Y.Opens) : f ⁻¹ᵁ U = g ⁻¹ᵁ U := by
  ext x
  change f x ∈ U ↔ g x ∈ U
  rw [equalDualReduction_point X f g h]

def equalDualReductionOpenMap (U : Y.Opens) : (g ⁻¹ᵁ U).toScheme ⟶ U.toScheme :=
  f.resLE U (g ⁻¹ᵁ U) (equalDualReduction_preimage X f g h U).ge

theorem equalDualReductionOpenMap_square (U : Y.Opens) :
    equalDualReductionOpenMap X f g h U ≫ U.ι = (g ⁻¹ᵁ U).ι ≫ f :=
  f.resLE_comp_ι _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EqualReductionOpenSquares
