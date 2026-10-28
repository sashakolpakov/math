import OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification
import OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimensionDrop

/-! # Stratum Dimension -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric

noncomputable section

/-!
# Native dimensions of smooth strata and singular boundaries

The bounds below concern the canonical transcendence dimensions of actual
function fields. A locally closed immersion is factored through its genuine
coborder open subscheme, where it is a closed immersion. The closed-immersion
inequality and the open-immersion equality give the bound for every integral
smooth stratum. Generic smoothness and strict dimension drop for proper
irreducible closed supports give the strict singular-boundary bound.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {K : Type u} [Field K] {X Y : Scheme.{u}}

/-- The native natural-number dimension cannot increase under an actual
closed immersion of integral schemes locally of finite type over the field. -/
theorem StratumDimension.schemeTranscendenceDimension_closedImmersion_le [IsIntegral X] [IsIntegral Y]
    (i : Y ⟶ X) [IsClosedImmersion i] (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ f) ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ f)
  apply (Nat.cast_le (α := Cardinal)).mp
  rw [Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_cast (i ≫ f), Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_cast f]
  exact Foundations.Scheme.ClosedImmersionDimension.closedImmersion_functionField_trdeg_le i f

/-- An actual locally closed immersion between integral schemes cannot
increase native dimension. The factorization and both dimension comparisons
are constructed from the given immersion. -/
theorem StratumDimension.schemeTranscendenceDimension_immersion_le [IsIntegral X] [IsIntegral Y]
    (i : Y ⟶ X) [IsImmersion i] (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ f) ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  let : Nonempty i.coborderRange := ⟨i.liftCoborder (genericPoint Y)⟩
  let : IsIntegral i.coborderRange.toScheme :=
    isIntegral_of_isOpenImmersion i.coborderRange.ι
  have h := StratumDimension.schemeTranscendenceDimension_closedImmersion_le i.liftCoborder
    (i.coborderRange.ι ≫ f)
  have he := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion i.coborderRange.ι f
  simpa only [← Category.assoc, Scheme.Hom.liftCoborder_ι] using h.trans_eq he

/-- Every actual integral smooth stratum has dimension at most the dimension
of its integral ambient scheme. No dimension bound is stored in the piece. -/
theorem IntegralSmoothStratification.IntegralSmoothGeometricPiece.dimension_le [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    P.dimension ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f :=
  StratumDimension.schemeTranscendenceDimension_immersion_le P.inclusion f

/-- The actual nonsmooth part of an integral support, viewed in the original
ambient scheme through its canonical closed immersion. -/
def StratumDimension.supportSingularBoundary (Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] : Set X :=
  (GenericPoint.reducedSupportι Z) '' SingularLocus.singularLocus (SupportFiniteType.supportStructureMap Z f)

theorem StratumDimension.isClosed_supportSingularBoundary (Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    IsClosed (StratumDimension.supportSingularBoundary Z f) :=
  (GenericPoint.reducedSupportι Z).isClosedEmbedding.isClosedMap _
    (SingularLocus.isClosed_singularLocus (SupportFiniteType.supportStructureMap Z f))

theorem StratumDimension.supportSingularBoundary_subset (Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    StratumDimension.supportSingularBoundary Z f ⊆ (Z : Set X) := by
  intro x hx
  rw [← GenericPoint.range_reducedSupportι Z]
  obtain ⟨y, _, rfl⟩ := hx
  exact Set.mem_range_self y

variable [PerfectField K]

/-- Generic smoothness excludes the actual generic point of the support from
its singular boundary in the ambient scheme. -/
theorem StratumDimension.genericPoint_not_mem_supportSingularBoundary (Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    irreducibleSetEquivPoints Z ∉ StratumDimension.supportSingularBoundary Z f := by
  rw [← GenericPoint.reducedSupport_genericPoint_eq Z]
  rintro ⟨x, hx, he⟩
  have hxgen := (GenericPoint.reducedSupportι Z).isClosedEmbedding.injective he
  apply SingularLocus.genericPoint_not_mem_singularLocus (SupportFiniteType.supportStructureMap Z f)
  simpa only [hxgen] using hx

/-- Every irreducible closed support contained in the singular boundary is
properly contained in the original support. -/
theorem StratumDimension.lt_of_subset_supportSingularBoundary (W Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (hW : (W : Set X) ⊆ StratumDimension.supportSingularBoundary Z f) : W < Z := by
  apply lt_of_le_not_ge (hW.trans (StratumDimension.supportSingularBoundary_subset Z f))
  intro hZW
  apply StratumDimension.genericPoint_not_mem_supportSingularBoundary Z f
  exact hW (hZW (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem)

/-- A closed irreducible support lying in the actual singular boundary has
strictly smaller native dimension. -/
theorem StratumDimension.supportTranscendenceDimension_lt_of_subset_singularBoundary
    (W Z : IrreducibleCloseds X) (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (hW : (W : Set X) ⊆ StratumDimension.supportSingularBoundary Z f) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f < Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z f :=
  Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt W Z f
    (StratumDimension.lt_of_subset_supportSingularBoundary W Z f hW)

/-- The genuine dense smooth stratum of an integral support has exactly the
dimension of that support, through the actual generic-stalk isomorphism. -/
theorem StratumDimension.smoothStratum_dimension_eq_support (Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (SmoothStratum.smoothStratumToBase (SupportFiniteType.supportStructureMap Z f)) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z f :=
  Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion
    (SmoothStratum.smoothStratumι (SupportFiniteType.supportStructureMap Z f)) (SupportFiniteType.supportStructureMap Z f)

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- Any integral smooth locally closed stratum of the actual support has
native dimension bounded by the support's own dimension. -/
theorem DimensionCycles.DimensionCycleSupport.stratum_dimension_le (Z : DimensionCycles.DimensionCycleSupport V p)
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece Z.structureMap) :
    P.dimension ≤ Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 V.structureMap :=
  P.dimension_le Z.structureMap

/-- The ambient codimension of the support converts the preceding bound to
the exact ambient dimension grading used for algebraic cycles. -/
theorem DimensionCycles.DimensionCycleSupport.stratum_dimension_add_codimension_le (Z : DimensionCycles.DimensionCycleSupport V p)
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece Z.structureMap) :
    P.dimension + p ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap := by
  rw [← Z.dimension_add_codimension]
  exact Nat.add_le_add_right (Z.stratum_dimension_le P) p

/-- Singular-boundary supports have strictly greater ambient codimension than
the support whose singularities they lie in. -/
theorem DimensionCycles.DimensionCycleSupport.codimension_lt_of_subset_singularBoundary (Z : DimensionCycles.DimensionCycleSupport V p)
    (W : IrreducibleCloseds V.carrier)
    (hW : (W : Set V.carrier) ⊆ StratumDimension.supportSingularBoundary Z.1 V.structureMap) :
    p < DimensionCycles.dimensionCodimension V W := by
  have hlt := StratumDimension.supportTranscendenceDimension_lt_of_subset_singularBoundary
    W Z.1 V.structureMap hW
  have hZ := Z.dimension_add_codimension
  have hWdim := DimensionCycles.supportDimension_add_dimensionCodimension V W
  omega

end

end OAI.AlgebraicGeometry.CycleClass.Geometric
