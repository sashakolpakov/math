import OAI.RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Reduction Opens -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReductionOpens

noncomputable section

/-! The actual reduction of the dual-number product is a surjective
closed immersion. Every open of the product is the inverse image of its
reduction, and affine opens reduce to affine opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

instance dualNumberOrigin_closed : IsClosedImmersion (LieRanks.dualNumberOrigin ℂ).left :=
  IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (LieRanks.dualNumberReduction ℂ))
    (fun a => ⟨(a, 0), rfl⟩)

instance dualBaseChangeReduction_closed (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    IsClosedImmersion (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left := by
  let : MorphismProperty.IsStableUnderComposition (@IsClosedImmersion.{0}) :=
    ⟨fun a b ha hb => by
      let := ha
      let := hb
      infer_instance⟩
  have ht : IsClosedImmersion (LieRanks.dualNumberOrigin ℂ ⊗ₘ 𝟙 X).left :=
    Picard.PoincareBundle.Product.Covers.property_tensor (@IsClosedImmersion) (LieRanks.dualNumberOrigin ℂ) (𝟙 X)
      inferInstance (by change IsClosedImmersion (𝟙 X.left); infer_instance)
  have hi : IsClosedImmersion (λ_ X).inv.left := by
    change IsClosedImmersion ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso (λ_ X)).inv
    infer_instance
  have hc : IsClosedImmersion ((λ_ X).inv.left ≫ (LieRanks.dualNumberOrigin ℂ ⊗ₘ 𝟙 X).left) :=
    IsClosedImmersion.comp _ _
  have h : (λ_ X).inv ≫ (LieRanks.dualNumberOrigin ℂ ⊗ₘ 𝟙 X) = RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction]
  exact (congrArg Over.Hom.left h) ▸ hc

theorem dualBaseChangeReduction_projection (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X ≫ snd (LieRanks.dualNumberTest ℂ) X = 𝟙 X := by
  simp [RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction]

theorem dualBaseChangeReduction_projection_point (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (x : X.left) :
    (snd (LieRanks.dualNumberTest ℂ) X).left ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left x) = x :=
  congrArg (fun f : X ⟶ X => f.left x) (dualBaseChangeReduction_projection X)

theorem dualOpen_eq_preimage_reduction (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    (U : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) :
    (snd (LieRanks.dualNumberTest ℂ) X).left ⁻¹ᵁ ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U) = U := by
  ext y
  obtain ⟨x, rfl⟩ := (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction_surjective X).surj y
  change (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left
      ((snd (LieRanks.dualNumberTest ℂ) X).left ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left x)) ∈ U ↔
    (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left x ∈ U
  rw [dualBaseChangeReduction_projection_point]

theorem dualAffineOpen_reduction (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    (U : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U) :=
  hU.preimage (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReductionOpens
