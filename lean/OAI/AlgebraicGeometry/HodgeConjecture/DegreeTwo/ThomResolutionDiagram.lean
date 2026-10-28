import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularThomSourceSheaf
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupSheafHomotopy

/-! # Thom Resolution Diagram -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomResolutionDiagram.Constructions

noncomputable section

section

/-! The source–Thom sheaf comparison is independent of the chosen normalized cocycle. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)

theorem regularThomZeroSheafMap_eq
    (hab : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 b) :
    RegularThomSourceSheaf.Constructions.regularThomZeroSheafMap Z a = RegularThomSourceSheaf.Constructions.regularThomZeroSheafMap Z b := by
  obtain ⟨h⟩ := RelativeCupSheafHomotopy.Constructions.relativeTwoCupGoodShiftSheaf_homotopic_of_class_eq
    (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen a b hab
  exact h.homologyMap_eq 0

variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)
variable (hb : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 b = Z.regularThomClass)

theorem regularSourceThomZeroSheafIso_eq :
    RegularThomSourceSheaf.Constructions.regularSourceThomZeroSheafIso Z a ha = RegularThomSourceSheaf.Constructions.regularSourceThomZeroSheafIso Z b hb := by
  have := LocalStalkQuasiIso.Constructions.moduleSheaf_localQuotient_epi (RegularThomSourceSheaf.Constructions.regularSourceZeroSheafMap Z)
    (RegularThomSourceSheaf.Constructions.regularThomZeroSheafMap Z a) (RegularThomSourceSheaf.Constructions.regularSourceThom_localQuotients Z a ha)
  apply Iso.ext
  apply (cancel_epi (RegularThomSourceSheaf.Constructions.regularSourceZeroSheafMap Z)).mp
  rw [RegularThomSourceSheaf.Constructions.regularSourceThomZeroSheafIso_comm, RegularThomSourceSheaf.Constructions.regularSourceThomZeroSheafIso_comm]
  exact regularThomZeroSheafMap_eq Z a b (ha.trans hb.symm)

theorem regularSourceThomSheafIso_eq :
    RegularThomSourceSheaf.Constructions.regularSourceThomSheafIso Z a ha = RegularThomSourceSheaf.Constructions.regularSourceThomSheafIso Z b hb := by
  unfold RegularThomSourceSheaf.Constructions.regularSourceThomSheafIso
  rw [regularSourceThomZeroSheafIso_eq Z a b ha hb]

end

/-! A coherent diagram of the actual source and Thom resolutions, including the original cup map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

theorem cochainZeroHomologyAugmentation_naturality {C : Type*} [Category C] [Abelian C]
    {K L : CochainComplex C ℕ} (f : K ⟶ L) :
    (CochainComplex.single₀ C).map (HomologicalComplex.homologyMap f 0) ≫
        ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation L =
      ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K ≫ f := by
  apply (CochainComplex.fromSingle₀Equiv L (K.homology 0)).injective
  apply Subtype.ext
  change ((CochainComplex.single₀ C).map (HomologicalComplex.homologyMap f 0) ≫
    ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation L).f 0 = (ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K ≫ f).f 0
  simp only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero,
    ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation_f_zero]
  rw [← Category.assoc, CochainComplex.isoHomologyπ₀_inv_naturality,
    Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc]

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

def regularSourceToThomResolution :
    (CochainComplex.single₀ _).obj ((RegularThomSourceSheaf.Constructions.regularSourceSheafComplex Z).homology 0) ⟶
      GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z :=
  (CochainComplex.single₀ _).map (RegularThomSourceSheaf.Constructions.regularSourceThomZeroSheafIso Z a ha).hom ≫
    ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation (GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)

theorem regularSourceToThomResolution_quasiIso : QuasiIso (regularSourceToThomResolution Z a ha) := by
  have := ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation_quasiIso (GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)
    (GoodShiftCohomology.Constructions.regularThomGoodShift_positive_homology_isZero Z)
  unfold regularSourceToThomResolution
  infer_instance

/-- The original normalized cup fits this diagram as a literal cochain-map equality. -/
theorem regularSourceToThomResolution_cup :
    (CochainComplex.single₀ _).map (RegularThomSourceSheaf.Constructions.regularSourceZeroSheafMap Z) ≫
        regularSourceToThomResolution Z a ha =
      ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation
        (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ)
          (TopCat.of Z.regularAmbientSpace))) ≫
        RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap (TopCat.of Z.regularAmbientSpace)
          Z.regularThomComplementOpen a := by
  unfold regularSourceToThomResolution
  rw [← Category.assoc, ← Functor.map_comp, RegularThomSourceSheaf.Constructions.regularSourceThomZeroSheafIso_comm]
  exact cochainZeroHomologyAugmentation_naturality _

theorem regularSourceResolution_pullback :
    (CochainComplex.single₀ _).map (RegularThomSourceSheaf.Constructions.regularSourceZeroSheafMap Z) ≫
        ClosedSourceResolution.Constructions.closedSourceSheafAugmentation (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) =
      ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation
        (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ)
          (TopCat.of Z.regularAmbientSpace))) ≫
        SingularSheafPullback.Constructions.singularSheafPullbackMap (ModuleCat.of ℚ ℚ) (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) :=
  cochainZeroHomologyAugmentation_naturality _

theorem regularSourceToThomResolution_eq
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
    (hb : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 b = Z.regularThomClass) :
    regularSourceToThomResolution Z a ha = regularSourceToThomResolution Z b hb := by
  unfold regularSourceToThomResolution
  rw [regularSourceThomZeroSheafIso_eq Z a b ha hb]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomResolutionDiagram.Constructions
