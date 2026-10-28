import OAI.AlgebraicGeometry.ComplexPoints.Analytic.CycleStratumRealization
import OAI.AlgebraicGeometry.CycleClass.Geometric.StratumClosure

/-! # Stratum Dimension Bounds -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.StratumDimensionBounds

noncomputable section

/-!
# Dimension bounds for the actual analytic manifolds of smooth strata

The analytic models here are those already constructed on native complex
points. Their dimensions are identified with the actual function fields,
then bounded by the algebraic immersion and support-dimension theorems.
No dimension data are added to a stratum or its analytic realization.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

namespace IntegralSmoothGeometricPiece

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}

/-- The derived complex dimension of a smooth stratum is bounded by the
native function-field dimension of its integral ambient scheme. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.complexDimension_le [IsIntegral X] [LocallyOfFiniteType f]
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    P.complexDimension ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  rw [P.complexDimension_eq_dimension]
  exact P.dimension_le f

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticModel_complex_finrank_le [IsIntegral X] [LocallyOfFiniteType f]
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    Module.finrank ℂ P.analyticModel ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  rw [P.analyticModel_complex_finrank]
  exact P.dimension_le f

/-- The real model dimension is bounded by twice the algebraic dimension. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticModel_real_finrank_le [IsIntegral X] [LocallyOfFiniteType f]
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    Module.finrank ℝ P.analyticModel ≤ 2 * Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  rw [P.analyticModel_real_finrank]
  exact Nat.mul_le_mul_left 2 (P.dimension_le f)

/-- The model dimension equals the function-field dimension of the
stratum's genuine reduced irreducible closure. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.complexDimension_eq_closure [NoetherianSpace X]
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    P.complexDimension = Foundations.Scheme.SupportDimension.supportTranscendenceDimension P.closureSupport f :=
  P.complexDimension_eq_dimension.trans P.dimension_eq_closure

/-- An actual inclusion of the stratum's image in a closed support gives
the corresponding complex-dimension bound. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.complexDimension_le_of_support_subset [NoetherianSpace X]
    [LocallyOfFiniteType f] (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f)
    (Z : IrreducibleCloseds X) (hP : P.support ⊆ (Z : Set X)) :
    P.complexDimension ≤ Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z f := by
  rw [P.complexDimension_eq_dimension]
  exact P.dimension_le_of_support_subset Z hP

/-- A stratum lying in the actual singular boundary of an irreducible
support has strictly smaller complex dimension. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.complexDimension_lt_of_support_subset_singularBoundary
    [NoetherianSpace X] [LocallyOfFiniteType f]
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) (Z : IrreducibleCloseds X)
    (hP : P.support ⊆ CycleClass.Geometric.StratumDimension.supportSingularBoundary Z f) :
    P.complexDimension < Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z f := by
  rw [P.complexDimension_eq_dimension]
  exact P.dimension_lt_of_support_subset_singularBoundary Z hP

/-- The strict algebraic drop is a drop of at least two in the actual
real model dimension. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.analyticModel_real_finrank_add_two_le_of_support_subset_singularBoundary
    [NoetherianSpace X] [LocallyOfFiniteType f]
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece f) (Z : IrreducibleCloseds X)
    (hP : P.support ⊆ CycleClass.Geometric.StratumDimension.supportSingularBoundary Z f) :
    Module.finrank ℝ P.analyticModel + 2 ≤ 2 * Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z f := by
  rw [P.analyticModel_real_finrank]
  have h := P.dimension_lt_of_support_subset_singularBoundary Z hP
  omega

end IntegralSmoothGeometricPiece

private theorem finiteTypeSource_noetherianSpace {X : Scheme}
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] [QuasiCompact f] :
    NoetherianSpace X := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : IsNoetherian X := ⟨⟩
  infer_instance

namespace DimensionCycleSupport

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- Every smooth stratum of the reduced support has complex dimension at
most that of its actual regular locus. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.stratum_complexDimension_le (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece Z.structureMap) :
    P.complexDimension ≤ Z.regularComplexDimension := by
  rw [P.complexDimension_eq_dimension, Z.regularComplexDimension_eq_supportDimension]
  exact Z.stratum_dimension_le P

/-- The support's codimension gives the expected ambient analytic bound. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.stratum_complexDimension_add_codimension_le (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece Z.structureMap) :
    P.complexDimension + p ≤ V.complexDimension := by
  rw [P.complexDimension_eq_dimension]
  exact (Z.stratum_dimension_add_codimension_le P).trans_eq
    (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension V.structureMap)

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.stratum_complexDimension_le_sub (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece Z.structureMap) :
    P.complexDimension ≤ V.complexDimension - p := by
  rw [← Z.regularComplexDimension_eq_sub]
  exact Z.stratum_complexDimension_le P

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.stratum_analyticModel_complex_finrank_le (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece Z.structureMap) :
    Module.finrank ℂ P.analyticModel ≤ V.complexDimension - p := by
  rw [P.analyticModel_complex_finrank, ← P.complexDimension_eq_dimension]
  exact Z.stratum_complexDimension_le_sub P

/-- Every stratum has real model dimension at most twice the support
dimension, expressed in the actual ambient codimension grading. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.stratum_analyticModel_real_finrank_le (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece Z.structureMap) :
    Module.finrank ℝ P.analyticModel ≤ 2 * (V.complexDimension - p) := by
  rw [P.analyticModel_real_finrank, ← P.complexDimension_eq_dimension]
  exact Nat.mul_le_mul_left 2 (Z.stratum_complexDimension_le_sub P)

/-- Equivalently, each stratum has real codimension at least twice the
algebraic codimension of the support. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.stratum_analyticModel_real_finrank_add_codimension_le
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece Z.structureMap) :
    Module.finrank ℝ P.analyticModel + 2 * p ≤ Module.finrank ℝ V.analyticModel := by
  rw [P.analyticModel_real_finrank, V.analyticModel_real_finrank,
    ← P.complexDimension_eq_dimension]
  have h := Z.stratum_complexDimension_add_codimension_le P
  omega

/-- The same bound for a piece already included in the ambient variety,
using only the actual inclusion of its support in the cycle support. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.ambientStratum_complexDimension_le_sub (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece V.structureMap)
    (hP : P.support ⊆ (Z.1 : Set V.carrier)) :
    P.complexDimension ≤ V.complexDimension - p := by
  let : NoetherianSpace V.carrier := finiteTypeSource_noetherianSpace V.structureMap
  rw [← Z.regularComplexDimension_eq_sub, Z.regularComplexDimension_eq_supportDimension]
  exact P.complexDimension_le_of_support_subset Z.1 hP

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.ambientStratum_analyticModel_real_finrank_le (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece V.structureMap)
    (hP : P.support ⊆ (Z.1 : Set V.carrier)) :
    Module.finrank ℝ P.analyticModel ≤ 2 * (V.complexDimension - p) := by
  rw [P.analyticModel_real_finrank, ← P.complexDimension_eq_dimension]
  exact Nat.mul_le_mul_left 2 (Z.ambientStratum_complexDimension_le_sub P hP)

/-- The genuine singular boundary of a codimension-p support contains
only strata of strictly smaller complex dimension than the support. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryStratum_complexDimension_lt_sub
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece V.structureMap)
    (hP : P.support ⊆ CycleClass.Geometric.StratumDimension.supportSingularBoundary Z.1 V.structureMap) :
    P.complexDimension < V.complexDimension - p := by
  let : NoetherianSpace V.carrier := finiteTypeSource_noetherianSpace V.structureMap
  rw [← Z.regularComplexDimension_eq_sub, Z.regularComplexDimension_eq_supportDimension]
  exact P.complexDimension_lt_of_support_subset_singularBoundary Z.1 hP

/-- The real codimension of every actual singular-boundary stratum inside
the support is at least two. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryStratum_analyticModel_real_finrank_add_two_le
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece V.structureMap)
    (hP : P.support ⊆ CycleClass.Geometric.StratumDimension.supportSingularBoundary Z.1 V.structureMap) :
    Module.finrank ℝ P.analyticModel + 2 ≤ 2 * (V.complexDimension - p) := by
  rw [P.analyticModel_real_finrank, ← P.complexDimension_eq_dimension]
  have h := Z.singularBoundaryStratum_complexDimension_lt_sub P hP
  omega

/-- Intrinsic formulation on the actual reduced support scheme. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularLocusStratum_complexDimension_lt_sub (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece Z.structureMap)
    (hP : P.support ⊆ CycleClass.Geometric.SingularLocus.singularLocus Z.structureMap) :
    P.complexDimension < V.complexDimension - p := by
  let : NoetherianSpace Z.scheme := finiteTypeSource_noetherianSpace Z.structureMap
  rw [P.complexDimension_eq_dimension, ← Z.regularComplexDimension_eq_sub,
    Z.regularComplexDimension_eq_supportDimension]
  exact P.dimension_lt_of_support_subset_singularLocus hP

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularLocusStratum_analyticModel_real_finrank_add_two_le
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece Z.structureMap)
    (hP : P.support ⊆ CycleClass.Geometric.SingularLocus.singularLocus Z.structureMap) :
    Module.finrank ℝ P.analyticModel + 2 ≤ 2 * (V.complexDimension - p) := by
  rw [P.analyticModel_real_finrank, ← P.complexDimension_eq_dimension]
  have h := Z.singularLocusStratum_complexDimension_lt_sub P hP
  omega

/-- In any actual geometric stratification of the singular boundary,
membership in its finite list supplies the support condition automatically. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.singularBoundaryStratification_piece_real_finrank_add_two_le
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (Q : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification V.structureMap
      (CycleClass.Geometric.StratumDimension.supportSingularBoundary Z.1 V.structureMap))
    {P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece V.structureMap} (hP : P ∈ Q.pieces) :
    Module.finrank ℝ P.analyticModel + 2 ≤ 2 * (V.complexDimension - p) :=
  Z.singularBoundaryStratum_analyticModel_real_finrank_add_two_le P
    (Q.piece_support_subset hP)

end DimensionCycleSupport

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.StratumDimensionBounds
