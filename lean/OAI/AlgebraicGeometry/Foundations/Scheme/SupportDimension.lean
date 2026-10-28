import OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.SupportAffineQuotient

/-! # Support Dimension -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimension

noncomputable section

/-!
# Dimension of genuine irreducible closed supports

The dimension is the transcendence degree of the function field of the actual
reduced induced support scheme. On every nonempty ambient affine chart it is
the transcendence degree of the genuine quotient coordinate ring, or of its
fraction field. This file makes no identification with order-theoretic coheight.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- The transcendence dimension of an irreducible support with its actual
reduced scheme structure and induced structural morphism. -/
def supportTranscendenceDimension (Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) : ℕ :=
  TranscendenceDimension.schemeTranscendenceDimension (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)

/-- This dimension is computed in the true function field of the support. -/
theorem supportTranscendenceDimension_def (Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)
    supportTranscendenceDimension Z f =
      (Algebra.trdeg K (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField).toNat := rfl

/-- Local finite type guarantees that the natural number retains the full
cardinal-valued transcendence degree of the support. -/
theorem supportTranscendenceDimension_cast (Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)
    (supportTranscendenceDimension Z f : Cardinal) =
      Algebra.trdeg K (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField :=
  TranscendenceDimension.schemeTranscendenceDimension_cast (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)

/-- The support dimension can be computed on any nonempty affine chart of the
ambient scheme by its actual quotient coordinate ring. -/
theorem supportTranscendenceDimension_eq_affineQuotient
    (Z : IrreducibleCloseds X) (f : X ⟶ Spec (.of K)) (U : X.affineOpens)
    [Nonempty (SupportAffineQuotient.supportAffineOpen Z U)] :
    letI := SupportAffineQuotient.supportAffineQuotientScalarAlgebra Z f U
    supportTranscendenceDimension Z f =
      (Algebra.trdeg K (SupportAffineQuotient.supportAffineQuotient Z U)).toNat := by
  let := SpecScalarTransport.specSectionScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) (SupportAffineQuotient.supportAffineOpen Z U)
  let := SupportAffineQuotient.supportAffineQuotientScalarAlgebra Z f U
  exact (TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)
    (SupportAffineQuotient.supportAffineOpen Z U) (SupportAffineQuotient.supportAffineOpen_isAffine Z U)).trans
      (congrArg Cardinal.toNat (SupportAffineQuotient.supportAffineSectionsAlgEquiv Z f U).trdeg_eq)

/-- The same affine formula expressed in the fraction field of the quotient. -/
theorem supportTranscendenceDimension_eq_affineFractionRing
    (Z : IrreducibleCloseds X) (f : X ⟶ Spec (.of K)) (U : X.affineOpens)
    [Nonempty (SupportAffineQuotient.supportAffineOpen Z U)] :
    letI := SupportAffineQuotient.supportAffineQuotientScalarAlgebra Z f U
    supportTranscendenceDimension Z f =
      (Algebra.trdeg K (FractionRing (SupportAffineQuotient.supportAffineQuotient Z U))).toNat := by
  let := SupportAffineQuotient.supportAffineQuotientScalarAlgebra Z f U
  exact (supportTranscendenceDimension_eq_affineQuotient Z f U).trans
    (congrArg Cardinal.toNat (TranscendenceDegreeTransfer.trdeg_eq_fractionRing K (SupportAffineQuotient.supportAffineQuotient Z U)))

/-- The quotient-to-function-field map respects the canonical base scalars. -/
theorem supportAffineQuotientFunctionField_isScalarTower
    (Z : IrreducibleCloseds X) (f : X ⟶ Spec (.of K)) (U : X.affineOpens)
    [Nonempty (SupportAffineQuotient.supportAffineOpen Z U)] :
    letI := SupportAffineQuotient.supportAffineQuotientScalarAlgebra Z f U
    letI := SupportAffineQuotient.supportAffineQuotientFunctionFieldAlgebra Z U
    letI := FunctionFieldScalar.functionFieldScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)
    IsScalarTower K (SupportAffineQuotient.supportAffineQuotient Z U) (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField := by
  let := SpecScalarTransport.specSectionScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) (SupportAffineQuotient.supportAffineOpen Z U)
  let := SupportAffineQuotient.supportAffineQuotientScalarAlgebra Z f U
  let := SupportAffineQuotient.supportAffineQuotientFunctionFieldAlgebra Z U
  let := FunctionFieldScalar.functionFieldScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)
  let := FunctionFieldScalar.functionFieldScalar_isScalarTower (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) (SupportAffineQuotient.supportAffineOpen Z U)
  apply IsScalarTower.of_algebraMap_eq'
  ext r
  change algebraMap K (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField r =
    algebraMap Γ(CycleClass.Geometric.GenericPoint.reducedSupportScheme Z, SupportAffineQuotient.supportAffineOpen Z U)
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField
        ((SupportAffineQuotient.supportAffineSectionsEquiv Z U).symm (algebraMap K (SupportAffineQuotient.supportAffineQuotient Z U) r))
  rw [IsScalarTower.algebraMap_apply K
    Γ(CycleClass.Geometric.GenericPoint.reducedSupportScheme Z, SupportAffineQuotient.supportAffineOpen Z U) (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField]
  exact congrArg
    (algebraMap Γ(CycleClass.Geometric.GenericPoint.reducedSupportScheme Z, SupportAffineQuotient.supportAffineOpen Z U)
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField)
    ((SupportAffineQuotient.supportAffineSectionsAlgEquiv Z f U).symm.commutes r).symm

/-- The quotient fraction field is canonically isomorphic over the actual base
field to the function field of the reduced support. -/
def supportFunctionFieldEquivAffineFractionRing
    (Z : IrreducibleCloseds X) (f : X ⟶ Spec (.of K)) (U : X.affineOpens)
    [Nonempty (SupportAffineQuotient.supportAffineOpen Z U)] :
    letI := SupportAffineQuotient.supportAffineQuotientScalarAlgebra Z f U
    letI := FunctionFieldScalar.functionFieldScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField ≃ₐ[K] FractionRing (SupportAffineQuotient.supportAffineQuotient Z U) := by
  letI := SupportAffineQuotient.supportAffineQuotientScalarAlgebra Z f U
  letI := FunctionFieldScalar.functionFieldScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)
  letI := SupportAffineQuotient.supportAffineQuotientFunctionFieldAlgebra Z U
  letI := supportAffineQuotientFunctionField_isScalarTower Z f U
  letI := SupportAffineQuotient.supportAffineQuotient_isFractionRing Z U
  exact ((FractionRing.algEquiv (SupportAffineQuotient.supportAffineQuotient Z U)
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField).symm).restrictScalars K

/-- A genuine irreducible closed support has dimension at most that of its
integral ambient scheme. Local finite type makes the natural-number comparison
faithful to the proved function-field transcendence-degree comparison. -/
theorem supportTranscendenceDimension_le [IsIntegral X]
    (Z : IrreducibleCloseds X) (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    supportTranscendenceDimension Z f ≤ TranscendenceDimension.schemeTranscendenceDimension f := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := FunctionFieldScalar.functionFieldScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f)
  apply (Nat.cast_le (α := Cardinal)).mp
  rw [supportTranscendenceDimension_cast Z f, TranscendenceDimension.schemeTranscendenceDimension_cast f]
  exact ClosedImmersionDimension.closedImmersion_functionField_trdeg_le (CycleClass.Geometric.GenericPoint.reducedSupportι Z) f

end

end OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimension
