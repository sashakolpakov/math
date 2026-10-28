import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalSupportCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedSourceThomNaturality

/-! # Local Support Naturality -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalSupportNaturality.Constructions

noncomputable section

section

/-! Actual relative support enlargement inside a neighborhood commutes with the source–Thom isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

theorem regularSourceThomLocalSupportIso_support_naturality
    (U : Opens Z.regularAmbientSpace) {B D : Opens U} (h : B ≤ D) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (𝟙 (TopCat.of ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)))
      (show Set.MapsTo (𝟙 (TopCat.of ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)))
        ((SingularSheafPullback.Constructions.openPreimageMap (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) U) ⁻¹' (B : Set U))
        ((SingularSheafPullback.Constructions.openPreimageMap (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) U) ⁻¹' (D : Set U)) from fun _ hx => h hx) q ≫
      (LocalSupportCup.Constructions.regularSourceThomLocalSupportIso Z a ha U B q).hom =
    (LocalSupportCup.Constructions.regularSourceThomLocalSupportIso Z a ha U D q).hom ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
        (show Set.MapsTo (𝟙 (TopCat.of U))
          (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
            (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U ∪ (B : Set U))
          (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
            (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U ∪ (D : Set U))
          from fun _ hx => Set.union_subset_union_right _ h hx) (2+q) := by
  let hO := NormalSupportRelative.Constructions.localSupportAmbientOpen_mono (X := TopCat.of Z.regularAmbientSpace) U h
  exact SupportedSourceThomNaturality.Constructions.sourceTargetIso_naturality
    (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) S q)
      (NormalSupportRelative.Constructions.localSupportAmbientOpen_source (X := TopCat.of Z.regularAmbientSpace) U D (RegularTopGysin.Constructions.regularSourceInclusionMap V Z))))
    (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) S q)
      (NormalSupportRelative.Constructions.localSupportAmbientOpen_source (X := TopCat.of Z.regularAmbientSpace) U B (RegularTopGysin.Constructions.regularSourceInclusionMap V Z))))
    (SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso Z a ha (NormalSupportRelative.Constructions.localSupportAmbientOpen (X := TopCat.of Z.regularAmbientSpace) U D) U q)
    (SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso Z a ha (NormalSupportRelative.Constructions.localSupportAmbientOpen (X := TopCat.of Z.regularAmbientSpace) U B) U q)
    (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) S (2+q))
      (NormalSupportRelative.Constructions.localSupportAmbientOpen_union (X := TopCat.of Z.regularAmbientSpace) U D Z.regularThomComplementOpen)))
    (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) S (2+q))
      (NormalSupportRelative.Constructions.localSupportAmbientOpen_union (X := TopCat.of Z.regularAmbientSpace) U B Z.regularThomComplementOpen))) _ _ _ _
    (NormalSupportRelative.Constructions.relativePairMap_supportEquality (𝟙 (TopCat.of ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)))
      (NormalSupportRelative.Constructions.localSupportAmbientOpen_source (X := TopCat.of Z.regularAmbientSpace) U B (RegularTopGysin.Constructions.regularSourceInclusionMap V Z))
      (NormalSupportRelative.Constructions.localSupportAmbientOpen_source (X := TopCat.of Z.regularAmbientSpace) U D (RegularTopGysin.Constructions.regularSourceInclusionMap V Z))
      (fun _ hx => hO hx) (fun _ hx => h hx) q)
    (SupportedSourceThomNaturality.Constructions.regularSourceThomSupportedRelativeIso_support_naturality Z a ha hO U q)
    (NormalSupportRelative.Constructions.relativePairMap_supportEquality (𝟙 (TopCat.of U))
      (NormalSupportRelative.Constructions.localSupportAmbientOpen_union (X := TopCat.of Z.regularAmbientSpace) U B Z.regularThomComplementOpen)
      (NormalSupportRelative.Constructions.localSupportAmbientOpen_union (X := TopCat.of Z.regularAmbientSpace) U D Z.regularThomComplementOpen)
      (fun _ hx => (sup_le_sup_left hO Z.regularThomComplementOpen) hx)
      (fun _ hx => Set.union_subset_union_right _ h hx) (2+q))

end

/-! Normalizing equal source and target supports preserves a natural relative isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

theorem relativeNormalizedSupportIso_eq (X Y : TopCat.{0}) (q r : ℕ)
    {A B S : Set X} {C D T : Set Y} (hAB : A ⊆ B) (hCD : C ⊆ D)
    (iA : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A q ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y C r)
    (iB : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y D r)
    (eA : A = S) (eB : B = S) (eC : C = T) (eD : D = T)
    (hn : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 X)
        (fun _ hx => hAB hx) q ≫ iA.hom =
      iB.hom ≫ AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 Y)
        (fun _ hx => hCD hx) r) :
    (eqToIso (congrArg (fun W => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X W q) eA)).inv ≫
        iA.hom ≫ (eqToIso (congrArg (fun W => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y W r) eC)).hom =
      (eqToIso (congrArg (fun W => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X W q) eB)).inv ≫
        iB.hom ≫ (eqToIso (congrArg (fun W => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y W r) eD)).hom := by
  subst S
  subst B
  subst T
  subst D
  simpa only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id,
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id] using hn

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalSupportNaturality.Constructions
