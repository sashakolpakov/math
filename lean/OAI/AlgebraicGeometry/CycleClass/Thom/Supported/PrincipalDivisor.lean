import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.DivisorDetection
import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum

/-! # Principal Divisor -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Supported.PrincipalDivisor

noncomputable section

/-! The actual finite sum of divisor cycle classes, with coefficients given
by the scheme's order function and support in an algebraic open complement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum.AlgebraicLineBundle

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Finite.DivisorDetection.Constructions

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  (R : X.carrier.Opens)

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
local notation "O" => OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X R
local notation "V" => OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum.Construction.integralPresentationVariety X

/-- The same point closure, with the established dimension grading. -/
def complementDivisorSupport (z : (Finite.DivisorDetection.Constructions.ComplementDivisorPoint X R)) : Geometric.DimensionCycles.DimensionCycleSupport V 1 :=
  DivisorClass.Chern.Component.Construction.integralSupportToVariety V 1 (DivisorClass.Chern.Geometric.Construction.pointDivisorSupport X ⟨z.val, z.property.1⟩)

theorem complementDivisorSupport_injective : Function.Injective (complementDivisorSupport X R) := by
  intro z w h
  apply Subtype.ext
  apply irreducibleSetEquivPoints.symm.injective
  exact congrArg (fun Z : Geometric.DimensionCycles.DimensionCycleSupport V 1 => Z.val) h

/-- Its actual complex support misses the reference open. -/
theorem complementDivisorSupport_complement (z : (Finite.DivisorDetection.Constructions.ComplementDivisorPoint X R)) :
    (O : Set T) ⊆ (Set.range (complementDivisorSupport X R z).analyticInclusion)ᶜ := by
  intro x hx hZ
  rw [(complementDivisorSupport X R z).range_analyticInclusion] at hZ
  have hs : closure ({z.val} : Set X.carrier) ⊆ (R : Set X.carrier)ᶜ :=
    closure_minimal (Set.singleton_subset_iff.mpr z.property.2) R.isOpen.isClosed_compl
  exact hs hZ hx

/-- The original supported cycle class, enlarged to the actual reference support. -/
def complementDivisorSupportedClass (z : (Finite.DivisorDetection.Constructions.ComplementDivisorPoint X R)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 T)
    (complementDivisorSupport_complement X R z) 2 (complementDivisorSupport X R z).rationalSupportedCycleClass

/-- Forgetting the enlarged support recovers the original absolute Thom cycle class. -/
theorem complementDivisorSupportedClass_absolute (z : (Finite.DivisorDetection.Constructions.ComplementDivisorPoint X R)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) T (O : Set T) 2
      (complementDivisorSupportedClass X R z) = (complementDivisorSupport X R z).rationalCycleClass := by
  have h := ConcreteCategory.congr_hom
    (Geometric.RelativeCohomologyExtensionNaturality.Cohomology.relativeCohomologyInclusion_naturality (ModuleCat.of ℚ ℚ) (𝟙 T)
      (complementDivisorSupport_complement X R z) 2) (complementDivisorSupport X R z).rationalSupportedCycleClass
  rw [AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id, Category.comp_id] at h
  exact h

variable [Nonempty R]
local instance : Fintype (Finite.DivisorDetection.Constructions.ComplementDivisorPoint X R) := Fintype.ofFinite _

variable (g : X.carrier.functionField)

/-- Sum the genuine supported cycle classes with their original algebraic orders. -/
def principalDivisorSupportedClass :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) 2 :=
  ∑ z : (Finite.DivisorDetection.Constructions.ComplementDivisorPoint X R), (X.carrier.ord g z.val : ℚ) • complementDivisorSupportedClass X R z

/-- The same finite divisor in the existing integral-variety cycle interface. -/
def principalDivisorCycle : Geometric.DimensionCycles.RationalDimensionCycle V 1 :=
  ∑ z : (Finite.DivisorDetection.Constructions.ComplementDivisorPoint X R),
    Finsupp.single (complementDivisorSupport X R z) (X.carrier.ord g z.val : ℚ)

/-- The supported sum forgets to the previously defined Thom cycle-class
map applied to the same finite actual divisor. -/
theorem principalDivisorSupportedClass_absolute :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) T (O : Set T) 2 (principalDivisorSupportedClass X R g) =
      (V).rationalCycleClass 1 (principalDivisorCycle X R g) := by
  unfold principalDivisorSupportedClass principalDivisorCycle
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_smul, complementDivisorSupportedClass_absolute X R, Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalCycleClass_single]

/-- Every support coefficient is exactly its previously defined algebraic order. -/
theorem principalDivisorCycle_apply (z : (Finite.DivisorDetection.Constructions.ComplementDivisorPoint X R)) :
    principalDivisorCycle X R g (complementDivisorSupport X R z) = (X.carrier.ord g z.val : ℚ) := by
  classical
  unfold principalDivisorCycle
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single z]
  · exact Finsupp.single_eq_same
  · intro w _ hw
    exact Finsupp.single_eq_of_ne (fun h => hw (complementDivisorSupport_injective X R h.symm))
  · simp

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Supported.PrincipalDivisor
