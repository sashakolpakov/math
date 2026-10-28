import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Module
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.FiniteDivisorDetection

/-! # Supported Principal Divisor -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportedPrincipalDivisor

noncomputable section

/-! The finite supported sum of canonical prime-divisor classes with the
actual algebraic orders of a rational function on a general smooth scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions
  SchemeDivisor.Module.Constructions FiniteDivisorDetection.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (R : X.left.Opens)

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "O" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X R

abbrev complementDivisorSupport (z : FiniteDivisorDetection.Constructions.ComplementDivisorPoint X R) : IrreducibleCloseds X.left :=
  SchemeDivisor.Purity.Constructions.primeSupport X ⟨z.val, z.property.1⟩

omit [IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem complementDivisorSupport_complement (z : FiniteDivisorDetection.Constructions.ComplementDivisorPoint X R) :
    (O : Set T) ⊆ (Set.range (RegularSupport.Constructions.supportInclusion X (complementDivisorSupport X R z)))ᶜ := by
  intro x hx hZ
  rw [RegularSupport.Constructions.supportInclusion_range] at hZ
  have hs : closure ({z.val} : Set X.left) ⊆ (R : Set X.left)ᶜ :=
    closure_minimal (Set.singleton_subset_iff.mpr z.property.2) R.isOpen.isClosed_compl
  exact hs hZ hx

/-- The actual supported class enlarged to the complement of the given unit open. -/
def complementDivisorSupportedClass (z : FiniteDivisorDetection.Constructions.ComplementDivisorPoint X R) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 T)
    (complementDivisorSupport_complement X R z) 2 (SchemeDivisor.Module.Constructions.supportedDivisorClass X ⟨z.val, z.property.1⟩)

variable [Nonempty R]
local instance : Fintype (FiniteDivisorDetection.Constructions.ComplementDivisorPoint X R) := Fintype.ofFinite _

/-- Every coefficient is the original scheme order, including negative pole orders. -/
def principalDivisorSupportedClass (g : X.left.functionField) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) 2 :=
  ∑ z : FiniteDivisorDetection.Constructions.ComplementDivisorPoint X R, (X.left.ord g z.val : ℚ) • complementDivisorSupportedClass X R z

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportedPrincipalDivisor
