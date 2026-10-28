import OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalSpecializationGrading
import OAI.AlgebraicGeometry.Divisors.LineBundles.Ord

/-! # Global Specialization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.GlobalSpecialization.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: specialization on genuine dimension-graded global cycles

The proved support-dimension theorem puts every coefficient of the global
specialization into the required grade. The resulting linear map recovers
the complete ungraded specialization when the grading is forgotten.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme}

/-- Scheme points whose actual reduced closures have the prescribed dimension. -/
def SchemeDimensionCyclePoint (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ) :=
  {x : X // Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f = d}

def schemeDimensionPointEmbedding (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ) :
    SchemeDimensionCyclePoint f d ↪ X := ⟨Subtype.val, Subtype.val_injective⟩

/-- Forget the grading of a finite rational cycle without altering its coefficients. -/
def schemeDimensionCycleInclusion (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ) :
    (SchemeDimensionCyclePoint f d →₀ ℚ) →ₗ[ℚ] (X →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (schemeDimensionPointEmbedding f d)

variable [AlgebraicGeometry.IsNoetherian X] (I : X.IdealSheafData)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

/-- The actual global prime specialization, regarded in its proved dimension grade. -/
def globalGradedPrimeSpecialization (d : ℕ) (x : SchemeDimensionCyclePoint f d) :
    SchemeDimensionCyclePoint (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d →₀ ℚ :=
  Finsupp.comapDomain (schemeDimensionPointEmbedding (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d)
    (Global.CycleSpecialization.BundleCycles.globalPrimeSpecializationQ I x.1)
    (schemeDimensionPointEmbedding (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d).injective.injOn

/-- The grading retains every nonzero specialization coefficient. -/
theorem globalGradedPrimeSpecialization_push [LocallyOfFiniteType f]
    (d : ℕ) (x : SchemeDimensionCyclePoint f d) :
    schemeDimensionCycleInclusion (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d
        (globalGradedPrimeSpecialization I f d x) = Global.CycleSpecialization.BundleCycles.globalPrimeSpecializationQ I x.1 := by
  have hs : ((Global.CycleSpecialization.BundleCycles.globalPrimeSpecializationQ I x.1).support : Set (Global.SpecialFiber.BundleCycles.globalSpecialFiber I)) ⊆
      Set.range (schemeDimensionPointEmbedding (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d) := by
    intro y hy
    refine ⟨⟨y, ?_⟩, rfl⟩
    exact (GlobalSpecializationGrading.BundleCycles.globalPrimeSpecializationQ_dimension I f x.1 y (Finsupp.mem_support_iff.mp hy)).trans x.2
  exact (Finsupp.embDomain_eq_mapDomain
    (schemeDimensionPointEmbedding (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d)
    (globalGradedPrimeSpecialization I f d x)).symm.trans (Finsupp.embDomain_comapDomain hs)

/-- Global specialization as a linear map on finite cycles of a fixed dimension. -/
def globalGradedCycleSpecialization (d : ℕ) :
    (SchemeDimensionCyclePoint f d →₀ ℚ) →ₗ[ℚ]
      (SchemeDimensionCyclePoint (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d →₀ ℚ) :=
  Finsupp.linearCombination ℚ (globalGradedPrimeSpecialization I f d)

@[simp]
theorem globalGradedCycleSpecialization_single (d : ℕ) (x : SchemeDimensionCyclePoint f d) (q : ℚ) :
    globalGradedCycleSpecialization I f d (Finsupp.single x q) =
      q • globalGradedPrimeSpecialization I f d x :=
  Finsupp.linearCombination_single ℚ q x

/-- Forgetting the dimension grading commutes with specialization on every finite rational cycle. -/
theorem globalGradedCycleSpecialization_push [LocallyOfFiniteType f] (d : ℕ) :
    (schemeDimensionCycleInclusion (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d).comp
        (globalGradedCycleSpecialization I f d) =
      (Global.CycleSpecialization.BundleCycles.globalCycleSpecialization I).comp (schemeDimensionCycleInclusion f d) :=
  (Finsupp.lmapDomain_linearCombination ℚ (schemeDimensionPointEmbedding f d)
    (schemeDimensionCycleInclusion (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d)
    (globalGradedPrimeSpecialization_push I f d)).symm

end

/-!
# LineBundleCycles: graded principal divisors on general finite-type schemes

The deformation and its cone need not be smooth or projective. Their
rational-equivalence relations use the same local-ring orders on actual
reduced integral supports. The dimension proof ensures that grading a
principal divisor discards no coefficient.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable {X : Scheme} [AlgebraicGeometry.IsNoetherian X]

/-- The complete principal divisor pushed from an actual integral support. -/
def schemePrincipalPointDivisor (W : IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) : X →₀ ℚ :=
  Finsupp.embDomain ⟨CycleClass.Geometric.GenericPoint.reducedSupportι W, (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective⟩
    ((Ord.BundleCycles.principalDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) g).mapRange (fun n : ℤ => (n : ℚ)) Int.cast_zero)

@[simp]
theorem schemePrincipalPointDivisor_at_support (W : IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (x : CycleClass.Geometric.GenericPoint.reducedSupportScheme W) :
    schemePrincipalPointDivisor W g (CycleClass.Geometric.GenericPoint.reducedSupportι W x) =
      ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).ord g x : ℚ) := Finsupp.embDomain_apply_self _ _ _

/-- Every nonzero principal-divisor coefficient has support dimension one lower. -/
theorem schemePrincipalPointDivisor_dimension (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (W : IrreducibleCloseds X) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField)
    (x : X) (hx : schemePrincipalPointDivisor W g x ≠ 0) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f + 1 =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f := by
  have hr : x ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι W) := by
    by_contra h
    exact hx (Finsupp.embDomain_of_notMem_range _ _ _ h)
  obtain ⟨y, rfl⟩ := hr
  have hy : coheight y = 1 := by
    by_contra h
    apply hx
    exact (schemePrincipalPointDivisor_at_support W g y).trans
      ((congrArg (fun n : ℤ => (n : ℚ)) (Scheme.ord_eq_zero_of_coheight_neq_one h g)).trans Int.cast_zero)
  have hd := DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one (CycleClass.Geometric.SupportFiniteType.supportStructureMap W f) y hy
  exact (congrArg (fun n => n + 1)
    (Point.SupportDimension.BundleCycles.pointClosure_dimension_closedImmersion (CycleClass.Geometric.GenericPoint.reducedSupportι W) f y)).trans hd

variable (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

/-- The finite principal divisor indexed in the requested dimension grade. -/
def schemeGradedPrincipalDivisor (d : ℕ) (W : IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) : SchemeDimensionCyclePoint f d →₀ ℚ :=
  Finsupp.comapDomain (schemeDimensionPointEmbedding f d) (schemePrincipalPointDivisor W g)
    (schemeDimensionPointEmbedding f d).injective.injOn

/-- With the actual support dimension, grading retains the full principal divisor. -/
theorem schemeGradedPrincipalDivisor_push [LocallyOfFiniteType f] (d : ℕ)
    (W : IrreducibleCloseds X) (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    schemeDimensionCycleInclusion f d (schemeGradedPrincipalDivisor f d W g) =
      schemePrincipalPointDivisor W g := by
  have hs : ((schemePrincipalPointDivisor W g).support : Set X) ⊆
      Set.range (schemeDimensionPointEmbedding f d) := by
    intro x hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    have hd := schemePrincipalPointDivisor_dimension f W g x (Finsupp.mem_support_iff.mp hx)
    omega
  exact (Finsupp.embDomain_eq_mapDomain (schemeDimensionPointEmbedding f d)
    (schemeGradedPrincipalDivisor f d W g)).symm.trans (Finsupp.embDomain_comapDomain hs)

omit [AlgebraicGeometry.IsNoetherian X] in
/-- Forgetting the grade is injective on finite cycles. -/
theorem schemeDimensionCycleInclusion_injective (d : ℕ) :
    Function.Injective (schemeDimensionCycleInclusion f d) :=
  Finsupp.mapDomain_injective (schemeDimensionPointEmbedding f d).injective

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.GlobalSpecialization.BundleCycles
