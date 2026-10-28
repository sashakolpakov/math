import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportComparison

/-! # Closed Support Thom Resolution -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportThomResolution.Constructions

noncomputable section

section

/-! The coherent source–Thom comparison retains every specified closed support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

section General

variable {X : TopCat.{0}} (O U : Opens X)
variable (K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
variable (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (heK : ∀ n, K.ExactAt (n+1))
variable (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n)) (heL : ∀ n, L.ExactAt (n+1))

def closedSupportDerivedResolutionIso (e : K.homology 0 ≅ L.homology 0) (n : ℕ) :
    (((ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := X) O U).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n ≅
      (((ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := X) O U).mapHomologicalComplex (ComplexShape.up ℕ)).obj L).homology n :=
  ClosedSupportComparison.Constructions.closedSupportResolutionDerivedIso O U K hK heK n ≪≫
    ((ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := X) O U).rightDerived n).mapIso e ≪≫
    (ClosedSupportComparison.Constructions.closedSupportResolutionDerivedIso O U L hL heL n).symm

theorem closedSupportDerivedResolutionIso_comm
    (A : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
    (hA : ∀ n, TopCat.Sheaf.IsFlasque (A.X n)) (heA : ∀ n, A.ExactAt (n+1))
    (f : A ⟶ K) (g : A ⟶ L) (e : K.homology 0 ≅ L.homology 0)
    (he : HomologicalComplex.homologyMap f 0 ≫ e.hom = HomologicalComplex.homologyMap g 0) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := X) O U).mapHomologicalComplex (ComplexShape.up ℕ)).map f) n ≫
        (closedSupportDerivedResolutionIso O U K L hK heK hL heL e n).hom =
      HomologicalComplex.homologyMap
        (((ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := X) O U).mapHomologicalComplex (ComplexShape.up ℕ)).map g) n := by
  apply (cancel_mono (ClosedSupportComparison.Constructions.closedSupportResolutionDerivedIso O U L hL heL n).hom).mp
  simp only [closedSupportDerivedResolutionIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, ClosedSupportComparison.Constructions.closedSupportResolutionDerivedIso_naturality O U hA heA f hK heK,
    Category.assoc, ← Functor.map_comp, he,
    ClosedSupportComparison.Constructions.closedSupportResolutionDerivedIso_naturality O U hA heA g hL heL]

end General

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

def regularSourceThomClosedSupportIso (O U : Opens Z.regularAmbientSpace) (n : ℕ) :=
  closedSupportDerivedResolutionIso (X := TopCat.of Z.regularAmbientSpace) O U (RegularThomSourceSheaf.Constructions.regularSourceSheafComplex Z) (GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)
    (ClosedSourceResolution.Constructions.closedSourceSheaf_isFlasque (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)) (AllThomSource.Constructions.regularSourceSheaf_exact_positive Z)
    (ThomGoodShiftFlasque.Constructions.regularThomGoodShift_isFlasque Z) (AllThomSource.Constructions.regularThomGoodShift_exact_positive Z)
    (RegularThomSourceSheaf.Constructions.regularSourceThomZeroSheafIso Z a ha) n

theorem regularSourceThomClosedSupportIso_cup (O U : Opens Z.regularAmbientSpace) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) O U).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (SingularSheafPullback.Constructions.singularSheafPullbackMap (ModuleCat.of ℚ ℚ) (RegularTopGysin.Constructions.regularSourceInclusionMap V Z))) n ≫
        (regularSourceThomClosedSupportIso Z a ha O U n).hom =
      HomologicalComplex.homologyMap
        (((ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) O U).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap (TopCat.of Z.regularAmbientSpace)
            Z.regularThomComplementOpen a)) n :=
  closedSupportDerivedResolutionIso_comm (X := TopCat.of Z.regularAmbientSpace) O U
    (RegularThomSourceSheaf.Constructions.regularSourceSheafComplex Z) (GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)
    (ClosedSourceResolution.Constructions.closedSourceSheaf_isFlasque (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)) (AllThomSource.Constructions.regularSourceSheaf_exact_positive Z)
    (ThomGoodShiftFlasque.Constructions.regularThomGoodShift_isFlasque Z) (AllThomSource.Constructions.regularThomGoodShift_exact_positive Z)
    (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex (TopCat.of Z.regularAmbientSpace))
    (ClosedSupportIs.Constructions.regularAmbientSingularSheaf_isFlasque Z) (ClosedSupportIs.Constructions.regularAmbientSingularSheaf_exact_positive Z)
    (SingularSheafPullback.Constructions.singularSheafPullbackMap (ModuleCat.of ℚ ℚ) (RegularTopGysin.Constructions.regularSourceInclusionMap V Z))
    (RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen a)
    (RegularThomSourceSheaf.Constructions.regularSourceThomZeroSheafIso Z a ha) (RegularThomSourceSheaf.Constructions.regularSourceThomZeroSheafIso_comm Z a ha) n

theorem regularSourceThomClosedSupportIso_eq
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
    (hb : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 b = Z.regularThomClass) (O U : Opens Z.regularAmbientSpace) (n : ℕ) :
    regularSourceThomClosedSupportIso Z a ha O U n = regularSourceThomClosedSupportIso Z b hb O U n := by
  unfold regularSourceThomClosedSupportIso
  rw [ThomResolutionDiagram.Constructions.regularSourceThomZeroSheafIso_eq Z a b ha hb]

end

/-! Resolution comparisons commute with actual natural transformations of the support-section functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} (O U P W : Opens X)
variable (α : ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) O U ⟶ ClosedSupportIs.Constructions.closedSupportSectionFunctor P W)
variable (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
variable (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (heK : ∀ n, K.ExactAt (n+1))

theorem closedSupportResolutionDerivedIso_functor_naturality (n : ℕ) :
    HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app K) n ≫
        (ClosedSupportComparison.Constructions.closedSupportResolutionDerivedIso P W K hK heK n).hom =
      (ClosedSupportComparison.Constructions.closedSupportResolutionDerivedIso O U K hK heK n).hom ≫
        (NatTrans.rightDerived α n).app (K.homology 0) := by
  let I := FlasqueDerivedComparison.Constructions.rationalSheafInjectiveResolution (K.homology 0)
  let F := ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) O U
  let G := ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) P W
  let t := ResolutionHomotopy.Constructions.resolutionLift K heK I
  have hn : HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app K) n ≫
      HomologicalComplex.homologyMap ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map t) n =
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map t) n ≫
      HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app I.cocomplex) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun f => HomologicalComplex.homologyMap f n)
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).naturality t).symm
  have hd := InjectiveResolution.rightDerived_app_eq α I n
  change (NatTrans.rightDerived α n).app (K.homology 0) =
    (I.isoRightDerivedObj F n).hom ≫
      HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app I.cocomplex) n ≫
      (I.isoRightDerivedObj G n).inv at hd
  change HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app K) n ≫
      (HomologicalComplex.homologyMap ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map t) n ≫
        (I.isoRightDerivedObj G n).inv) =
    (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map t) n ≫
      (I.isoRightDerivedObj F n).inv) ≫ (NatTrans.rightDerived α n).app (K.homology 0)
  rw [hd]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hn, Category.assoc]

variable (L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
variable (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n)) (heL : ∀ n, L.ExactAt (n+1))

theorem closedSupportDerivedResolutionIso_functor_naturality
    (e : K.homology 0 ≅ L.homology 0) (n : ℕ) :
    HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app K) n ≫
        (closedSupportDerivedResolutionIso P W K L hK heK hL heL e n).hom =
      (closedSupportDerivedResolutionIso O U K L hK heK hL heL e n).hom ≫
        HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app L) n := by
  apply (cancel_mono (ClosedSupportComparison.Constructions.closedSupportResolutionDerivedIso P W L hL heL n).hom).mp
  simp only [closedSupportDerivedResolutionIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [closedSupportResolutionDerivedIso_functor_naturality O U P W α L hL heL]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [closedSupportResolutionDerivedIso_functor_naturality O U P W α K hK heK]
  rw [Category.assoc, ← (NatTrans.rightDerived α n).naturality e.hom, ← Category.assoc]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportThomResolution.Constructions
