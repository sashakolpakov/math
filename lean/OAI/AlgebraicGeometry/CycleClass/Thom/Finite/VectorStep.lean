import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionCup
import OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVector
import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.CupTargets

/-! # Vector Step -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Finite.VectorStep.Constructions

noncomputable section

/-! The genuine finite cycle cup with a regular-section vector
reduces to its actual principal step cupped with the remaining vector.
All classes, equations, and intersection supports are literal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Finite.CycleSectionClass.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity.Constructions.SupportedCupTargets OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Normal
open OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVector.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionChange.Constructions.Equation OAI.AlgebraicGeometry.CycleClass.Thom.Normal.CupTargets.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.CupDegrees.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.HeadTailCoordinates.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

variable (p n : ℕ) (B : V.carrier.Opens) [Nonempty B]
  (r : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (s : Fin n → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
  (U : Opens V.analyticSpace)
  (hU : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))
  {L K : Type} (u : L → U) (hu : IsOpen (Set.range u)ᶜ) (v : K → U) (hv : IsOpen (Set.range v)ᶜ)
  (ht : Set.MapsTo (BaseSectionVector.Constructions.baseSectionVector (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU n s) (Set.range v)ᶜ ({0}ᶜ))
  (c : Geometric.DimensionCycles.RationalDimensionCycle V p)
  (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 →
    (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ Set.range u)
  (hne : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p), c D ≠ 0 → Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B))
  (hr : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0), letI := hne D hD
    Affine.SectionFunction.Constructions.parentSectionFunction D B r ≠ 0)

local notation "j" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B
local notation "w" => OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions.baseSectionImage j U hU r
local notation "hw" => OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) r)
  (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) r)
local notation "S" => Set.range u ∩ Set.range w
local notation "G" => Set.range w ∩ Set.range v
local notation "F" => (Set.range u ∩ Set.range w) ∩ Set.range v

include hu in
theorem step_openComplement : IsOpen Sᶜ := by
  rw [← ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq u w]
  exact hu.union hw

include hv in
theorem vector_openComplement : IsOpen Gᶜ := by
  rw [← ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq w v]
  exact (hw).union hv

theorem stepComplement_eq : Sᶜ ∪ (Set.range v)ᶜ = Fᶜ := by
  ext x
  exact not_and_or.symm

theorem finalComplement_eq : (Set.range u)ᶜ ∪ Gᶜ = Fᶜ := by
  ext x
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff]
  tauto

include ht in
theorem vector_mapsTo : Set.MapsTo (BaseSectionVector.Constructions.baseSectionVector j U hU (n + 1) (Fin.cons r s)) Gᶜ ({0}ᶜ) := by
  have h := BaseSectionVector.Constructions.baseSectionVector_mapsTo j U hU n r s (Set.range w)ᶜ (Set.range v)ᶜ
    (BaseSectionChange.Constructions.Equation.baseSectionEquation_mapsTo j U hU r) ht
  rwa [ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq w v] at h

theorem head_tail_normalCup :
    EvenIntersectionAssociativity.Constructions.SupportedCupTargets.cupTo (TopCat.of U) (Set.range w)ᶜ (Set.range v)ᶜ Gᶜ hw hv (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq w v)
      2 (2 * n) (2 * (n + 1)) (by omega)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (BaseSectionChange.Constructions.Equation.baseSectionEquation j U hU r)
        (BaseSectionChange.Constructions.Equation.baseSectionEquation_mapsTo j U hU r) 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (BaseSectionVector.Constructions.baseSectionVector j U hU n s) ht (2 * n)
        (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass n)) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (BaseSectionVector.Constructions.baseSectionVector j U hU (n + 1) (Fin.cons r s))
      (vector_mapsTo V n B r s U hU v ht) (2 * (n + 1)) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (n + 1)) := by
  have hfg : Set.MapsTo (Normal.CupDegrees.Constructions.normalMapAt (BaseSectionChange.Constructions.Equation.baseSectionEquation j U hU r) (BaseSectionVector.Constructions.baseSectionVector j U hU n s)
      (HeadTailCoordinates.Constructions.headTailCoordinates n)) Gᶜ ({0}ᶜ) := by
    rw [BaseSectionVector.Constructions.baseSectionVector_normalMapAt]
    exact vector_mapsTo V n B r s U hU v ht
  exact (Normal.CupTargets.Constructions.normalCupTo (Set.range w)ᶜ (Set.range v)ᶜ Gᶜ hw hv (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq w v)
    1 n (n + 1) (Nat.add_comm 1 n) (BaseSectionChange.Constructions.Equation.baseSectionEquation j U hU r) (BaseSectionVector.Constructions.baseSectionVector j U hU n s)
    (HeadTailCoordinates.Constructions.headTailCoordinates n) (BaseSectionChange.Constructions.Equation.baseSectionEquation_mapsTo j U hU r) ht hfg).trans
      (ConcreteCategory.congr_hom (ThomOpenRestriction.Constructions.pairMap_congr (BaseSectionVector.Constructions.baseSectionVector_normalMapAt j U hU n r s) hfg
        (vector_mapsTo V n B r s U hU v ht) (2 * (n + 1))) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (n + 1)))

theorem cycle_vectorCup_eq_step_vectorCup :
    EvenIntersectionAssociativity.Constructions.SupportedCupTargets.cupTo (TopCat.of U) (Set.range u)ᶜ Gᶜ Fᶜ hu (vector_openComplement V B r U hU v hv)
      (finalComplement_eq V B r U hU u v) (2 * p) (2 * (n + 1)) (2 * ((p + 1) + n)) (by omega)
      (Open.SupportedLift.Constructions.Map.relativeClassMap V U (Set.range u) p (Open.SupportedLift.Constructions.restrictCycle V U (Set.range u) p c))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (BaseSectionVector.Constructions.baseSectionVector j U hU (n + 1) (Fin.cons r s))
        (vector_mapsTo V n B r s U hU v ht) (2 * (n + 1)) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (n + 1))) =
    EvenIntersectionAssociativity.Constructions.SupportedCupTargets.cupTo (TopCat.of U) Sᶜ (Set.range v)ᶜ Fᶜ (step_openComplement V B r U hU u hu) hv
      (stepComplement_eq V B r U hU u v) (2 * (p + 1)) (2 * n) (2 * ((p + 1) + n)) (Nat.mul_add 2 (p + 1) n).symm
      (Open.SupportedLift.Constructions.Map.relativeClassMap V U S (p + 1) (Open.SupportedLift.Constructions.restrictCycle V U S (p + 1) (CycleSectionClass.Constructions.cycleSectionStep V p B r U u c hc hne hr)))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (BaseSectionVector.Constructions.baseSectionVector j U hU n s) ht (2 * n)
        (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass n)) := by
  have h := EvenIntersectionAssociativity.Constructions.SupportedCupTargets.cupTo_associative (TopCat.of U) (Set.range u)ᶜ (Set.range w)ᶜ (Set.range v)ᶜ Sᶜ Gᶜ Fᶜ
    hu hw hv (step_openComplement V B r U hU u hu) (vector_openComplement V B r U hU v hv)
    (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq u w) (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq w v)
    (stepComplement_eq V B r U hU u v) (finalComplement_eq V B r U hU u v)
    (2 * p) 2 (2 * n) (2 * (p + 1)) (2 * (n + 1)) (2 * ((p + 1) + n))
    (by omega) (by omega) (by omega) (by omega)
    (Open.SupportedLift.Constructions.Map.relativeClassMap V U (Set.range u) p (Open.SupportedLift.Constructions.restrictCycle V U (Set.range u) p c))
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (BaseSectionChange.Constructions.Equation.baseSectionEquation j U hU r)
      (BaseSectionChange.Constructions.Equation.baseSectionEquation_mapsTo j U hU r) 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1))
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (BaseSectionVector.Constructions.baseSectionVector j U hU n s) ht (2 * n)
      (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass n))
  rw [SectionCup.Constructions.cycle_sectionEquationCup_eq_step V p B r U hU u hu c hc hne hr,
    head_tail_normalCup V n B r s U hU v hv ht] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Finite.VectorStep.Constructions
