import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportedSourceCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportRelative

/-! # Local Support Cup -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.LocalSupportCup.Constructions.Construction

noncomputable section

section

/-! The supported source–Thom isomorphism for any actual open complement inside a neighborhood. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions

set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

def regularSourceThomLocalSupportIso (U : Opens Z.regularAmbientSpace) (B : Opens U) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U))
      ((HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.openPreimageMap (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) U) ⁻¹' (B : Set U)) q ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
        (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U ∪ (B : Set U)) ((2 * p)+q) :=
  (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)) S q)
      (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen_source (X := TopCat.of Z.regularAmbientSpace) U B (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)))).symm ≪≫
    SupportedThomSource.Constructions.Construction.regularSourceThomSupportedRelativeIso Z a ha (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen (X := TopCat.of Z.regularAmbientSpace) U B) U q ≪≫
    eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) S ((2 * p)+q))
      (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen_union (X := TopCat.of Z.regularAmbientSpace) U B Z.regularThomComplementOpen))

end

/-! The local-support source–Thom comparison is normalized by the actual two-support cup. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions

set_option backward.isDefEq.respectTransparency false

theorem twoSupportCup_rightSupportEquality (X : TopCat.{0}) (A : Set X) {B B' : Set X}
    (eB : B = B') (hA : IsOpen A) (hB : IsOpen B) (hB' : IsOpen B') (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p) :
    ModuleCat.ofHom (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p q a) ≫
      (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∪ S) (p+q)) eB)).hom =
    (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S q) eB)).hom ≫
      ModuleCat.ofHom (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X A B' hA hB' p q a) := by
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

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

theorem regularSourceThomLocalSupportIso_cup (U : Opens Z.regularAmbientSpace) (B : Opens U) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.openPreimageMap (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) U)
        (A := (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.openPreimageMap (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) U) ⁻¹' (B : Set U)) (B := (B : Set U))
        (fun _ hx => hx) q ≫ (regularSourceThomLocalSupportIso Z a ha U B q).hom =
      ModuleCat.ofHom (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
          (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U) (B : Set U)
        (Z.regularThomComplementOpen.isOpen.preimage continuous_subtype_val) B.isOpen (2 * p) q
        (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
          (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U (2 * p) Z.regularThomClass)) := by
  let f := SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z
  let O := HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen (X := TopCat.of Z.regularAmbientSpace) U B
  let eR := eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) S q)
    (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen_restriction (X := TopCat.of Z.regularAmbientSpace) U B))
  let eS := eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of ((Opens.map f).obj U)) S q) (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen_source (X := TopCat.of Z.regularAmbientSpace) U B f))
  let eT := eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) S ((2 * p)+q))
    (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen_union (X := TopCat.of Z.regularAmbientSpace) U B Z.regularThomComplementOpen))
  exact supportConjugateIso_cup eR eS eT (SupportedThomSource.Constructions.Construction.regularSourceThomSupportedRelativeIso Z a ha O U q) _ _ _ _
    (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.relativePairMap_supportEquality (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.openPreimageMap f U)
      (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen_source (X := TopCat.of Z.regularAmbientSpace) U B f) (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen_restriction (X := TopCat.of Z.regularAmbientSpace) U B)
      (fun _ hx => hx) (fun _ hx => hx) q)
    (twoSupportCup_rightSupportEquality (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
        (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U)
      (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen_restriction (X := TopCat.of Z.regularAmbientSpace) U B)
      (Z.regularThomComplementOpen.isOpen.preimage continuous_subtype_val)
      (O.isOpen.preimage continuous_subtype_val) B.isOpen (2 * p) q
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
        (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U (2 * p) Z.regularThomClass))
    (SupportedSourceCup.Constructions.Construction.regularSourceThomSupportedRelativeIso_cup Z a ha O U q)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.LocalSupportCup.Constructions.Construction
