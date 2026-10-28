import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportRelative

/-! # Local Support Cup -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalSupportCup.Constructions

noncomputable section

section

/-! The supported source–Thom isomorphism for any actual open complement inside a neighborhood. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

def regularSourceThomLocalSupportIso (U : Opens Z.regularAmbientSpace) (B : Opens U) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U))
      ((SingularSheafPullback.Constructions.openPreimageMap (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) U) ⁻¹' (B : Set U)) q ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
        (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U ∪ (B : Set U)) (2+q) :=
  (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) S q)
      (NormalSupportRelative.Constructions.localSupportAmbientOpen_source (X := TopCat.of Z.regularAmbientSpace) U B (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)))).symm ≪≫
    SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso Z a ha (NormalSupportRelative.Constructions.localSupportAmbientOpen (X := TopCat.of Z.regularAmbientSpace) U B) U q ≪≫
    eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) S (2+q))
      (NormalSupportRelative.Constructions.localSupportAmbientOpen_union (X := TopCat.of Z.regularAmbientSpace) U B Z.regularThomComplementOpen))

end

/-! The local-support source–Thom comparison is normalized by the actual two-support cup. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

theorem twoSupportCup_rightSupportEquality (X : TopCat.{0}) (A : Set X) {B B' : Set X}
    (eB : B = B') (hA : IsOpen A) (hB : IsOpen B) (hB' : IsOpen B') (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p) :
    ModuleCat.ofHom (SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p q a) ≫
      (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∪ S) (p+q)) eB)).hom =
    (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S q) eB)).hom ≫
      ModuleCat.ofHom (SupportCup.Constructions.twoSupportCohomologyCup X A B' hA hB' p q a) := by
  subst B'
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp]

theorem supportConjugateIso_cup {C : Type*} [Category C] {R R' S S' T T' : C}
    (eR : R ≅ R') (eS : S ≅ S') (eT : T ≅ T') (e : S ≅ T)
    (f : R ⟶ S) (f' : R' ⟶ S') (g : R ⟶ T) (g' : R' ⟶ T')
    (hf : f ≫ eS.hom = eR.hom ≫ f') (hg : g ≫ eT.hom = eR.hom ≫ g') (he : f ≫ e.hom = g) :
    f' ≫ (eS.symm ≪≫ e ≪≫ eT).hom = g' := by
  apply (cancel_epi eR.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← hf, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, he, hg]

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

theorem regularSourceThomLocalSupportIso_cup (U : Opens Z.regularAmbientSpace) (B : Opens U) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (SingularSheafPullback.Constructions.openPreimageMap (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) U)
        (A := (SingularSheafPullback.Constructions.openPreimageMap (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) U) ⁻¹' (B : Set U)) (B := (B : Set U))
        (fun _ hx => hx) q ≫ (regularSourceThomLocalSupportIso Z a ha U B q).hom =
      ModuleCat.ofHom (SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
          (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U) (B : Set U)
        (Z.regularThomComplementOpen.isOpen.preimage continuous_subtype_val) B.isOpen 2 q
        (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
          (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U 2 Z.regularThomClass)) := by
  let f := RegularTopGysin.Constructions.regularSourceInclusionMap V Z
  let O := NormalSupportRelative.Constructions.localSupportAmbientOpen (X := TopCat.of Z.regularAmbientSpace) U B
  let eR := eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) S q)
    (NormalSupportRelative.Constructions.localSupportAmbientOpen_restriction (X := TopCat.of Z.regularAmbientSpace) U B))
  let eS := eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of ((Opens.map f).obj U)) S q) (NormalSupportRelative.Constructions.localSupportAmbientOpen_source (X := TopCat.of Z.regularAmbientSpace) U B f))
  let eT := eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) S (2+q))
    (NormalSupportRelative.Constructions.localSupportAmbientOpen_union (X := TopCat.of Z.regularAmbientSpace) U B Z.regularThomComplementOpen))
  exact supportConjugateIso_cup eR eS eT (SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso Z a ha O U q) _ _ _ _
    (NormalSupportRelative.Constructions.relativePairMap_supportEquality (SingularSheafPullback.Constructions.openPreimageMap f U)
      (NormalSupportRelative.Constructions.localSupportAmbientOpen_source (X := TopCat.of Z.regularAmbientSpace) U B f) (NormalSupportRelative.Constructions.localSupportAmbientOpen_restriction (X := TopCat.of Z.regularAmbientSpace) U B)
      (fun _ hx => hx) (fun _ hx => hx) q)
    (twoSupportCup_rightSupportEquality (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
        (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U)
      (NormalSupportRelative.Constructions.localSupportAmbientOpen_restriction (X := TopCat.of Z.regularAmbientSpace) U B)
      (Z.regularThomComplementOpen.isOpen.preimage continuous_subtype_val)
      (O.isOpen.preimage continuous_subtype_val) B.isOpen 2 q
      (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
        (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U 2 Z.regularThomClass))
    (NormalSupportRelative.Constructions.regularSourceThomSupportedRelativeIso_cup Z a ha O U q)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalSupportCup.Constructions
