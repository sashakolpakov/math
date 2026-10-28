import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReductionOpens

/-! # Product -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Product

noncomputable section

section

/-! Reduction and projection restrict to a genuine retraction on
every open of the dual-number product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)

def dualOpenReduction : ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).toScheme ⟶ U.toScheme :=
  (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ∣_ U

def dualOpenProjection : U.toScheme ⟶ ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).toScheme :=
  (snd (LieRanks.dualNumberTest ℂ) X).left.resLE ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U) U
    (Dual.ReductionOpens.dualOpen_eq_preimage_reduction X U).ge

theorem dualOpenReduction_ι :
    dualOpenReduction X U ≫ U.ι =
      ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).ι ≫ (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left :=
  morphismRestrict_ι _ _

theorem dualOpenProjection_ι :
    dualOpenProjection X U ≫ ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).ι =
      U.ι ≫ (snd (LieRanks.dualNumberTest ℂ) X).left :=
  Scheme.Hom.resLE_comp_ι _ _

theorem dualOpenReduction_projection :
    dualOpenReduction X U ≫ dualOpenProjection X U =
      𝟙 ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).toScheme := by
  apply (cancel_mono ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).ι).mp
  rw [Category.assoc, dualOpenProjection_ι, ← Category.assoc, dualOpenReduction_ι,
    Category.assoc]
  have h := congrArg (fun f : X ⟶ X => f.left) (Dual.ReductionOpens.dualBaseChangeReduction_projection X)
  change (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ (snd (LieRanks.dualNumberTest ℂ) X).left = 𝟙 X.left at h
  rw [h, Category.comp_id, Category.id_comp]

end

section

/-! Every actual open of a dual-number product is the product of its
reduced open with the dual-number test, by an explicit scheme isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)

def dualReducedOpenOver : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).ι ≫ X.hom)

def dualReducedOpenInclusion : dualReducedOpenOver X U ⟶ X :=
  Over.homMk ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).ι rfl

def dualOpenProductMap : (LieRanks.dualNumberTest ℂ ⊗ dualReducedOpenOver X U).left ⟶
    (LieRanks.dualNumberTest ℂ ⊗ X).left :=
  (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ dualReducedOpenInclusion X U).left

instance dualOpenProductMap_isOpenImmersion : IsOpenImmersion (dualOpenProductMap X U) := by
  have hj : IsOpenImmersion (dualReducedOpenInclusion X U).left :=
    inferInstanceAs (IsOpenImmersion ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).ι)
  exact Picard.PoincareBundle.Product.Covers.property_tensor (@IsOpenImmersion) (𝟙 (LieRanks.dualNumberTest ℂ))
    (dualReducedOpenInclusion X U) (by change IsOpenImmersion (𝟙 (LieRanks.dualNumberTest ℂ).left); infer_instance) hj

theorem dualOpenProductMap_reduction (x : (dualReducedOpenOver X U).left) :
    dualOpenProductMap X U ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction (dualReducedOpenOver X U)).left x) =
      (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ((dualReducedOpenInclusion X U).left x) :=
  congrArg (fun f : dualReducedOpenOver X U ⟶ LieRanks.dualNumberTest ℂ ⊗ X => f.left x)
    (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction_natural (dualReducedOpenInclusion X U))

theorem dualOpenProductMap_range : Set.range (dualOpenProductMap X U) = Set.range U.ι := by
  rw [Scheme.Opens.range_ι]
  ext y
  change (∃ z, dualOpenProductMap X U z = y) ↔ y ∈ U
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction_surjective (dualReducedOpenOver X U)).surj z
    rw [dualOpenProductMap_reduction]
    exact x.property
  · intro hy
    obtain ⟨x, rfl⟩ := (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction_surjective X).surj y
    let a : (dualReducedOpenOver X U).left := ⟨x, hy⟩
    exact ⟨(RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction (dualReducedOpenOver X U)).left a,
      dualOpenProductMap_reduction X U a⟩

def dualOpenProductIso : (LieRanks.dualNumberTest ℂ ⊗ dualReducedOpenOver X U).left ≅ U.toScheme :=
  IsOpenImmersion.isoOfRangeEq (dualOpenProductMap X U) U.ι (dualOpenProductMap_range X U)

theorem dualOpenProductIso_hom_ι :
    (dualOpenProductIso X U).hom ≫ U.ι = dualOpenProductMap X U :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end

/-! The actual product-chart isomorphism identifies its zero fiber
with the original reduction morphism on the family open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem dualOpenProductIso_reduction (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) :
    (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction (dualReducedOpenOver X U)).left ≫ (dualOpenProductIso X U).hom =
      dualOpenReduction X U := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, dualOpenProductIso_hom_ι]
  have h := congrArg (fun f : dualReducedOpenOver X U ⟶ LieRanks.dualNumberTest ℂ ⊗ X => f.left)
    (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction_natural (dualReducedOpenInclusion X U))
  exact h.trans (dualOpenReduction_ι X U).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Product
