import OAI.AlgebraicGeometry.CycleClass.Geometric.RegularFixedNormalPair
import OAI.AlgebraicGeometry.CycleClass.Geometric.Extension
import OAI.AlgebraicGeometry.CycleClass.Geometric.GlobalSupportPurity
import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSupportGerm
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexThom
import Mathlib.Topology.Metrizable.Urysohn

/-! # Regular Thom -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RegularThom.DimensionCycleSupport

noncomputable section

/-!
# The actual Thom group of a cycle support's regular locus

The regular locus is the original native complex-point manifold, embedded
closedly in the complement of its singular boundary. Its codimension is the
cycle's actual algebraic codimension. The topology and lower support
vanishing needed by the global Thom construction are derived from this
proved geometry.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- The actual open ambient manifold is metrizable. This follows from the
proved compact Hausdorff second-countable topology of the projective variety. -/
instance _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientSpace_metrizable (Z : DimensionCycles.DimensionCycleSupport V p) :
    MetrizableSpace Z.regularAmbientSpace := by
  let : MetrizableSpace V.analyticSpace := inferInstance
  change MetrizableSpace {x : V.analyticSpace // x ∈ Z.analyticSingularBoundaryᶜ}
  infer_instance

/-- The open complement of the actual regular-locus image in its ambient
boundary complement. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomComplementOpen (Z : DimensionCycles.DimensionCycleSupport V p) :
    Opens Z.regularAmbientSpace :=
  EmbeddedSupportComplement.Cycles.embeddedSupportComplement Z.regularComplementInclusion
    Z.isClosedEmbedding_regularComplementInclusion

@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomComplementOpen_coe (Z : DimensionCycles.DimensionCycleSupport V p) :
    (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) =
      (Set.range Z.regularComplementInclusion)ᶜ := rfl

/-- The genuine rational relative cohomology group in the cycle's actual
Thom degree, with its actual open complement as the relative subspace. -/
abbrev _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomGroup (Z : DimensionCycles.DimensionCycleSupport V p) : ModuleCat.{0} ℚ :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
    (Set.range Z.regularComplementInclusion)ᶜ (2 * p)

/-- The degree in the general complex-immersion construction is exactly
the algebraic Thom degree of this cycle. This is only degree transport
between the same actual relative cohomology groups. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomDegreeIso (Z : DimensionCycles.DimensionCycleSupport V p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      (Set.range Z.regularComplementInclusion)ᶜ
      (2 * ComplexNormalAtlas.Cycles.complexImmersionCodimension Z.regularAnalyticModel V.analyticModel) ≅
        Z.regularThomGroup :=
  eqToIso (by rw [Z.regularComplement_complexImmersionCodimension])

/-- The genuine singular cochain sheaf complex supported on the regular
locus inside the boundary-complement manifold. -/
abbrev _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomSheafComplex (Z : DimensionCycles.DimensionCycleSupport V p) :=
  SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ)
    (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen

/-- The actual supported stalk cohomology vanishes below twice the cycle
codimension, by its proved closed complex immersion. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomStalk_isZero_below (Z : DimensionCycles.DimensionCycleSupport V p)
    (y : Z.regularAmbientSpace) (n : ℕ) (hn : n < 2 * p) :
    IsZero ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex Z.regularThomSheafComplex y).homology n) := by
  by_cases hy : y ∈ Set.range Z.regularComplementInclusion
  · obtain ⟨x, rfl⟩ := hy
    apply (Z.regularFixedNormalPair x).supportedStalk_homology_isZero_of_lt
      Z.regularThomComplementOpen rfl n
    simpa only [Module.finrank_fin_fun] using hn
  · exact SupportStalkVanishes.Cycles.supportedSingularSheaf_stalk_homology_isZero_of_mem
      (X := TopCat.of Z.regularAmbientSpace) (ModuleCat.of ℚ ℚ)
      Z.regularThomComplementOpen y hy n

/-- The corresponding actual global relative groups vanish in all lower
degrees. No purity premise is supplied by the caller. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomCohomology_isZero_below (Z : DimensionCycles.DimensionCycleSupport V p)
    (n : ℕ) (hn : n < 2 * p) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (Set.range Z.regularComplementInclusion)ᶜ n) := by
  exact GlobalSupportPurity.Cycles.supportCohomology_isZero_of_stalk (TopCat.of Z.regularAmbientSpace)
    Z.regularThomComplementOpen (2 * p) Z.regularThomStalk_isZero_below n hn

/-- The actual relative Thom-degree group is canonically the global
sections of its supported cohomology sheaf, by the proved lower vanishing. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomFirstCohomologyIso (Z : DimensionCycles.DimensionCycleSupport V p) :
    Z.regularThomGroup ≅
      (Z.regularThomSheafComplex.homology (2 * p)).obj.obj
        (op (⊤ : Opens (TopCat.of Z.regularAmbientSpace))) :=
  GlobalSupportPurity.Cycles.supportedGlobalFirstCohomologyIso_of_stalk (TopCat.of Z.regularAmbientSpace)
    Z.regularThomComplementOpen (2 * p) Z.regularThomStalk_isZero_below

/-- The actual normal-chart identification of a supported stalk in the
literal cycle degree. The normal coordinate space is the proved `ℂ^p`. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomStalkNormalIso (Z : DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex Z.regularThomSheafComplex
      (Z.regularComplementInclusion x)).homology (2 * p) ≅ ModuleCat.of ℚ ℚ :=
  (Z.regularFixedNormalPair x).supportedStalkNormalCohomologyIso
    Z.regularThomComplementOpen rfl (2 * p) ≪≫
      RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyIso p

/-- Read the normal coefficient of an actual global relative class by
taking its supported germ and the fixed complex normal coordinates. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomLocalCoefficient (Z : DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) : Z.regularThomGroup ⟶ ModuleCat.of ℚ ℚ :=
  Z.regularThomFirstCohomologyIso.hom ≫
    TopCat.Presheaf.germ (Z.regularThomSheafComplex.homology (2 * p)).presheaf
      ⊤ (Z.regularComplementInclusion x) trivial ≫
    (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCohomologyIso Z.regularThomSheafComplex
      (Z.regularComplementInclusion x) (2 * p)).inv ≫
    (Z.regularThomStalkNormalIso x).hom

/-- An actual relative class in the first support degree is determined by
its normal coefficients along the regular locus. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThom_ext (Z : DimensionCycles.DimensionCycleSupport V p) (a b : Z.regularThomGroup)
    (h : ∀ x, Z.regularThomLocalCoefficient x a = Z.regularThomLocalCoefficient x b) :
    a = b := by
  apply Z.regularThomFirstCohomologyIso.toLinearEquiv.injective
  apply TopCat.Presheaf.section_ext (Z.regularThomSheafComplex.homology (2 * p)) ⊤
  intro y _
  by_cases hy : y ∈ Set.range Z.regularComplementInclusion
  · obtain ⟨x, rfl⟩ := hy
    apply (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCohomologyIso Z.regularThomSheafComplex
      (Z.regularComplementInclusion x) (2 * p)).symm.toLinearEquiv.injective
    apply (Z.regularThomStalkNormalIso x).toLinearEquiv.injective
    exact h x
  · let : Subsingleton ((Z.regularThomSheafComplex.homology (2 * p)).presheaf.stalk y) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (SupportStalkVanishes.Cycles.supportedSingularSheaf_cohomologySheaf_stalk_isZero_of_mem
          (X := TopCat.of Z.regularAmbientSpace) (ModuleCat.of ℚ ℚ)
          Z.regularThomComplementOpen y hy (2 * p))
    exact Subsingleton.elim _ _

/-- Literal restriction to the normalized normal-chart class gives normal
coefficient one under the genuine supported-germ comparison. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomLocalCoefficient_of_restriction
    (Z : DimensionCycles.DimensionCycleSupport V p) (x : Z.regularAnalyticSpace)
    (a : Z.regularThomGroup)
    (ha : RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (Set.range Z.regularComplementInclusion)ᶜ
      (Z.regularFixedNormalPair x).openNeighborhood (2 * p) a =
        (Z.regularFixedNormalPair x).rationalClassFin) :
    Z.regularThomLocalCoefficient x a = 1 := by
  let P := Z.regularFixedNormalPair x
  have hg := ConcreteCategory.congr_hom
    (RelativeCohomologySections.Cycles.relativeCohomologyGlobalSectionMap_germ (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen
      P.openNeighborhood (Z.regularComplementInclusion x) P.point_mem_neighborhood
      (2 * p)) a
  simp only [ConcreteCategory.comp_apply] at hg
  have ha' : RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)
      P.openNeighborhood (2 * p) a = P.rationalClassFin := ha
  rw [ha'] at hg
  have hc := ConcreteCategory.congr_hom
    (NormalGermCompatibility.Cycles.relativeCohomologySectionMap_germ_cochain (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen
      P.openNeighborhood (Z.regularComplementInclusion x) P.point_mem_neighborhood
      (2 * p)) P.rationalClassFin
  simp only [ConcreteCategory.comp_apply] at hc
  have hgc := congrArg (fun z => (Z.regularThomStalkNormalIso x).hom
    ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCohomologyIso Z.regularThomSheafComplex
      (Z.regularComplementInclusion x) (2 * p)).inv z)) (hg.trans hc)
  have hvalue : Z.regularThomLocalCoefficient x a =
      (Z.regularThomStalkNormalIso x).hom
        (HomologicalComplex.homologyMap
          (AlgebraicTopology.Cohomology.Singular.SupportedStalk.relativeToSupportedStalkGerm (ModuleCat.of ℚ ℚ)
            (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen
            P.openNeighborhood (Z.regularComplementInclusion x) P.point_mem_neighborhood)
          (2 * p) P.rationalClassFin) := by
    unfold DimensionCycles.DimensionCycleSupport.regularThomLocalCoefficient DimensionCycles.DimensionCycleSupport.regularThomFirstCohomologyIso
    rw [ComplexThom.Cycles.supportedGlobalFirstCohomologyIso_hom_eq_sectionMap]
    exact hgc.trans (congrArg (Z.regularThomStalkNormalIso x).hom
      ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCohomologyIso Z.regularThomSheafComplex
        (Z.regularComplementInclusion x) (2 * p)).toLinearEquiv.symm_apply_apply _))
  rw [hvalue]
  change (RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyIso p).hom
    ((P.supportedStalkNormalCohomologyIso Z.regularThomComplementOpen rfl (2 * p)).hom
      (HomologicalComplex.homologyMap
        (AlgebraicTopology.Cohomology.Singular.SupportedStalk.relativeToSupportedStalkGerm (ModuleCat.of ℚ ℚ)
          (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen
          P.openNeighborhood (Z.regularComplementInclusion x) P.point_mem_neighborhood)
        (2 * p) P.rationalClassFin)) = 1
  rw [P.rationalClassFin_eq_normalPullback]
  have hn := ConcreteCategory.congr_hom
    (P.normalCohomologyMap_supportedStalkNormal
      Z.isClosedEmbedding_regularComplementInclusion.isClosed_range (2 * p))
    (RationalLocalPurity.Cycles.complexNormalRationalDualClass p)
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at hn
  exact (congrArg (RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyIso p).hom hn).trans
    (RationalLocalPurity.Cycles.complexNormalRationalDualClass_normalization p)

/-- The actual rational Thom class of the regular locus, with degree
fixed by the original algebraic codimension. All geometric hypotheses
of the global construction are discharged by the native immersion. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomClass (Z : DimensionCycles.DimensionCycleSupport V p) : Z.regularThomGroup :=
  Z.regularThomDegreeIso.hom
    (ComplexThom.Cycles.complexThomClass (E := Z.regularAnalyticModel) (F := V.analyticModel)
      Z.regularComplementInclusion (Z.contMDiff_regularComplementInclusion ω)
      Z.mfderiv_regularComplementInclusion_injective
      Z.isClosedEmbedding_regularComplementInclusion)

@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomClass_degree_inv (Z : DimensionCycles.DimensionCycleSupport V p) :
    Z.regularThomDegreeIso.inv Z.regularThomClass =
      ComplexThom.Cycles.complexThomClass (E := Z.regularAnalyticModel) (F := V.analyticModel)
        Z.regularComplementInclusion (Z.contMDiff_regularComplementInclusion ω)
        Z.mfderiv_regularComplementInclusion_injective
        Z.isClosedEmbedding_regularComplementInclusion :=
  Z.regularThomDegreeIso.toLinearEquiv.symm_apply_apply _

private theorem complexThomClass_restrict_of_codimension_eq
    {E F M N : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ω N]
    [MetrizableSpace N]
    (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x))
    (he : Topology.IsClosedEmbedding f) {q : ℕ}
    (hq : ComplexNormalAtlas.Cycles.complexImmersionCodimension E F = q) (x : M)
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin q → ℂ) f x)
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ, E × (Fin q → ℂ))) :
    RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ P.openNeighborhood (2 * q)
      ((eqToHom (congrArg (fun k => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of N) (Set.range f)ᶜ (2 * k)) hq))
        (ComplexThom.Cycles.complexThomClass f hf hi he)) =
      P.normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * q)
        (RationalLocalPurity.Cycles.complexNormalRationalDualClass q) := by
  subst q
  exact ComplexThom.Cycles.complexThomClass_restrict_normalPair f hf hi he x P hP

/-- In any genuine complex differentiable normal chart of the regular
support, the global class is the actual pullback of the standard normal
class. Thus the construction is independent of its chosen normal atlas. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomClass_restrict_normalPair (Z : DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace)
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ)
      Z.regularComplementInclusion x)
    (hP : P.ambientChart.MDifferentiable
      𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ))) :
    RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (Set.range Z.regularComplementInclusion)ᶜ
      P.openNeighborhood (2 * p) Z.regularThomClass =
      P.normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * p)
        (RationalLocalPurity.Cycles.complexNormalRationalDualClass p) :=
  complexThomClass_restrict_of_codimension_eq
    Z.regularComplementInclusion (Z.contMDiff_regularComplementInclusion ω)
    Z.mfderiv_regularComplementInclusion_injective
    Z.isClosedEmbedding_regularComplementInclusion
    Z.regularComplement_complexImmersionCodimension x P hP

/-- The literal restriction to the fixed `ℂ^p` normal chart is its
previously constructed, normalized local relative class. -/
@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomClass_restrict (Z : DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (Set.range Z.regularComplementInclusion)ᶜ
      (Z.regularFixedNormalPair x).openNeighborhood (2 * p) Z.regularThomClass =
        (Z.regularFixedNormalPair x).rationalClassFin := by
  rw [(Z.regularFixedNormalPair x).rationalClassFin_eq_normalPullback]
  exact Z.regularThomClass_restrict_normalPair x (Z.regularFixedNormalPair x)
    (Z.regularFixedNormalPair_ambientChart_mdifferentiable x)

/-- The actual regular-locus Thom class has coefficient one at every
regular point in the fixed complex normal coordinates. -/
@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomClass_normalization (Z : DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    Z.regularThomLocalCoefficient x Z.regularThomClass = 1 :=
  Z.regularThomLocalCoefficient_of_restriction x Z.regularThomClass
    (Z.regularThomClass_restrict x)

/-- The stated local normalizations uniquely specify the global class. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomClass_unique (Z : DimensionCycles.DimensionCycleSupport V p)
    (a : Z.regularThomGroup) (ha : ∀ x, Z.regularThomLocalCoefficient x a = 1) :
    a = Z.regularThomClass :=
  Z.regularThom_ext a Z.regularThomClass
    (fun x => (ha x).trans (Z.regularThomClass_normalization x).symm)

/-- Existence and uniqueness in the genuine relative group, with all
normalizations proved from the original algebraic support. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.existsUnique_regularThomClass (Z : DimensionCycles.DimensionCycleSupport V p) :
    ∃! a : Z.regularThomGroup, ∀ x, Z.regularThomLocalCoefficient x a = 1 :=
  ⟨Z.regularThomClass, Z.regularThomClass_normalization, Z.regularThomClass_unique⟩

/-- Every integral cycle support has a nonempty regular locus, so its
normalized relative Thom class is nonzero. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularThomClass_ne_zero (Z : DimensionCycles.DimensionCycleSupport V p) :
    Z.regularThomClass ≠ 0 := by
  obtain ⟨x⟩ := (inferInstance : Nonempty Z.regularAnalyticSpace)
  intro h
  have hn := Z.regularThomClass_normalization x
  rw [h, map_zero] at hn
  exact zero_ne_one hn

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RegularThom.DimensionCycleSupport
