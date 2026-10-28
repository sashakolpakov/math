import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalSupportNaturality

/-! # Local Support Representative -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalSupportRepresentative.Constructions

noncomputable section

section

/-! Restricting an ambient support complement and then representing it locally preserves the actual isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

theorem localSupportAmbientOpen_restriction_le {X : TopCat.{0}} (U O : Opens X) :
    NormalSupportRelative.Constructions.localSupportAmbientOpen U ((Opens.map (Opens.inclusion' (X := X) U)).obj O) ≤ O := by
  rintro y ⟨z, hz, rfl⟩
  exact hz

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

theorem regularSourceThomLocalSupportIso_ambient_restriction
    (U O : Opens Z.regularAmbientSpace) (q : ℕ) :
    (LocalSupportCup.Constructions.regularSourceThomLocalSupportIso Z a ha U
      ((Opens.map (Opens.inclusion' (X := TopCat.of Z.regularAmbientSpace) U)).obj O) q).hom =
      (SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso Z a ha O U q).hom := by
  let B := (Opens.map (Opens.inclusion' (X := TopCat.of Z.regularAmbientSpace) U)).obj O
  let C := NormalSupportRelative.Constructions.localSupportAmbientOpen (X := TopCat.of Z.regularAmbientSpace) U B
  let h := localSupportAmbientOpen_restriction_le (X := TopCat.of Z.regularAmbientSpace) U O
  have hn := LocalSupportNaturality.Constructions.relativeNormalizedSupportIso_eq
    (TopCat.of ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) (TopCat.of U) q (2+q)
    (show AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAnalyticSpace)
        (((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj C : Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace)
        ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U) ⊆
      AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAnalyticSpace)
        (((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace)
        ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U) from fun _ hx => h hx)
    (show AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
        ((Z.regularThomComplementOpen ⊔ C : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) U ⊆
      AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
        ((Z.regularThomComplementOpen ⊔ O : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) U
      from fun _ hx => (sup_le_sup_left h Z.regularThomComplementOpen) hx)
    (SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso Z a ha C U q)
    (SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso Z a ha O U q)
    (NormalSupportRelative.Constructions.localSupportAmbientOpen_source (X := TopCat.of Z.regularAmbientSpace) U B (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)) rfl
    (NormalSupportRelative.Constructions.localSupportAmbientOpen_union (X := TopCat.of Z.regularAmbientSpace) U B Z.regularThomComplementOpen) rfl
    (SupportedSourceThomNaturality.Constructions.regularSourceThomSupportedRelativeIso_support_naturality Z a ha h U q)
  simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.comp_id] at hn
  change (LocalSupportCup.Constructions.regularSourceThomLocalSupportIso Z a ha U B q).hom =
    𝟙 _ ≫ (SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso Z a ha O U q).hom at hn
  exact hn.trans (Category.id_comp _)

end

/-! The original and local support descriptions agree after transport to specified source and target supports. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

theorem regularSourceThomLocalSupportIso_ambient_restriction_cast
    (U O : Opens Z.regularAmbientSpace) (B : Opens U)
    (hB : (Opens.map (Opens.inclusion' (X := TopCat.of Z.regularAmbientSpace) U)).obj O = B)
    (S : Set ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) (T : Set U) (q : ℕ)
    (eS : AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAnalyticSpace)
      (((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace)
      ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U) = S)
    (eT : AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
      ((Z.regularThomComplementOpen ⊔ O : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) U = T)
    (eSB : (SingularSheafPullback.Constructions.openPreimageMap (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) U) ⁻¹' (B : Set U) = S)
    (eTB : AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
      (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U ∪ (B : Set U) = T) :
    (eqToIso (congrArg (fun W => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) W q) eS)).inv ≫
        (SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso Z a ha O U q).hom ≫
          (eqToIso (congrArg (fun W => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) W (2+q)) eT)).hom =
    (eqToIso (congrArg (fun W => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) W q) eSB)).inv ≫
        (LocalSupportCup.Constructions.regularSourceThomLocalSupportIso Z a ha U B q).hom ≫
          (eqToIso (congrArg (fun W => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) W (2+q)) eTB)).hom := by
  subst B
  rw [regularSourceThomLocalSupportIso_ambient_restriction]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalSupportRepresentative.Constructions
