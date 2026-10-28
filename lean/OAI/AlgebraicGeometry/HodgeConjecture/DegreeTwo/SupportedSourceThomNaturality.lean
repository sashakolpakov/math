import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSourceRelativeMap
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportNaturality
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedSourceThomIso

/-! # Supported Source Thom Naturality -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedSourceThomNaturality.Constructions

noncomputable section

/-! The source–Thom isomorphism commutes with actual relative support enlargement on both sides. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

theorem sourceTargetIso_naturality {C : Type*} [Category C]
    {S₁ S₂ A₁ A₂ T₁ T₂ B₁ B₂ : C}
    (s₁ : S₁ ≅ A₁) (s₂ : S₂ ≅ A₂) (t₁ : S₁ ≅ T₁) (t₂ : S₂ ≅ T₂)
    (u₁ : T₁ ≅ B₁) (u₂ : T₂ ≅ B₂)
    (a : A₁ ⟶ A₂) (s : S₁ ⟶ S₂) (t : T₁ ⟶ T₂) (b : B₁ ⟶ B₂)
    (hs : s ≫ s₂.hom = s₁.hom ≫ a) (ht : s ≫ t₂.hom = t₁.hom ≫ t)
    (hu : t ≫ u₂.hom = u₁.hom ≫ b) :
    a ≫ (s₂.symm ≪≫ t₂ ≪≫ u₂).hom = (s₁.symm ≪≫ t₁ ≪≫ u₁).hom ≫ b := by
  apply (cancel_epi s₁.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← hs, Category.assoc, Iso.hom_inv_id_assoc,
    ← Category.assoc, ht, Category.assoc, hu]

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

theorem regularSourceThomSupportedRelativeIso_support_naturality
    {C D : Opens Z.regularAmbientSpace} (h : C ≤ D) (U : Opens Z.regularAmbientSpace) (n : ℕ) :
    HomologicalComplex.homologyMap
        (ClosedSourceRelativeMap.Constructions.closedSourceRelativeSupportChange (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) h U) n ≫
        (SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso Z a ha C U n).hom =
      (SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso Z a ha D U n).hom ≫
        HomologicalComplex.homologyMap
          (IntersectSupportNaturality.Constructions.relativeOpenComplementChange (X := TopCat.of Z.regularAmbientSpace)
            (sup_le_sup_left h Z.regularThomComplementOpen) U) (2+n) := by
  exact sourceTargetIso_naturality
    (ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) D U n)
    (ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) C U n)
    (ClosedSupportThomResolution.Constructions.regularSourceThomClosedSupportIso Z a ha D U n)
    (ClosedSupportThomResolution.Constructions.regularSourceThomClosedSupportIso Z a ha C U n)
    (SupportedThomRelative.Constructions.regularThomClosedSupportRelativeIso Z D U n)
    (SupportedThomRelative.Constructions.regularThomClosedSupportRelativeIso Z C U n) _ _ _ _
    (ClosedSourceRelativeMap.Constructions.closedSourceSupportedRelativeCohomologyIso_support_naturality (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) h U n)
    (SupportSectionChanges.Constructions.regularSourceThomClosedSupportIso_naturality Z a ha D U C U
      (SupportSectionChanges.Constructions.closedSupportSectionChange (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) h U) n)
    (IntersectSupportNaturality.Constructions.regularThomClosedSupportRelativeIso_support_naturality Z h U n)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedSourceThomNaturality.Constructions
