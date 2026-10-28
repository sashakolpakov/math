import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Dimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationFiniteType
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportDimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.CycleSpecialization

/-! # Global Specialization Grading -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalSpecializationGrading.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: global specialization preserves support dimension

The divisor of the nonzero parameter lies in codimension one on the
integral support deformation. The dimension increase of that deformation
and dimension preservation under its two actual closed-fiber embeddings
show that every nonzero global specialization coefficient has the original
support dimension.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.Order

variable {X : Scheme} (I P : X.IdealSheafData)

/-- Both maps from the support fiber induce the same actual morphism to the base. -/
theorem globalSupportSpecialFiber_toBase :
    Support.Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P ≫
        (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P ≫ P.subschemeι) =
      Support.Specialization.BundleCycles.globalSupportSpecialFiberMap I P ≫ Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I := by
  have hl : Support.Projection.BundleCycles.globalSupportDeformationToSupport I P ≫ P.subschemeι =
      Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P ≫ Global.Deformation.BundleCycles.globalDeformationProjection I :=
    (Support.Projection.BundleCycles.globalSupportDeformationToSupport_toBase I P).trans (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap_toBase I P).symm
  have hp : Support.Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P ≫ Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P =
      Support.Specialization.BundleCycles.globalSupportSpecialFiberMap I P ≫ Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I := pullback.condition
  rw [hl, ← Category.assoc, hp, Category.assoc, Global.SpecialFiber.BundleCycles.globalSpecialFiberMap_toBase]

variable [AlgebraicGeometry.IsNoetherian X] [IsIntegral P.subscheme]

/-- A nonzero parameter-divisor coefficient has exactly the original support dimension. -/
theorem globalSupportParameterDivisor_dimension
    (f : P.subscheme ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (x : Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) (hx : Support.Specialization.BundleCycles.globalSupportParameterDivisor I P x ≠ 0) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x)
        (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P ≫ f) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  have hc : coheight x = 1 := by
    by_contra h
    apply hx
    exact Scheme.ord_eq_zero_of_coheight_neq_one h _
  have hg : LocallyOfFiniteType (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P) :=
    Global.DeformationFiniteType.BundleCycles.globalSupportDeformationToSupport_locallyOfFiniteType I P
  have hd := DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one
    (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P ≫ f) x hc
  have he := Deformation.Dimension.BundleCycles.globalSupportDeformation_dimension I P f
  omega

/-- Every nonzero coefficient on the global cone retains the integral support's dimension. -/
theorem globalClosedSupportSpecialization_dimension
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (x : Global.SpecialFiber.BundleCycles.globalSpecialFiber I) (hx : Support.Specialization.BundleCycles.globalClosedSupportSpecialization I P x ≠ 0) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x)
        (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (P.subschemeι ≫ f) := by
  have hr : x ∈ Set.range (Support.Specialization.BundleCycles.globalSupportSpecialFiberMap I P) := by
    by_contra h
    exact hx (Finsupp.embDomain_of_notMem_range _ _ _ h)
  obtain ⟨y, rfl⟩ := hr
  have hy : Support.Specialization.BundleCycles.globalSupportParameterDivisor I P (Support.Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P y) ≠ 0 :=
    fun h => hx ((Support.Specialization.BundleCycles.globalClosedSupportSpecialization_at_support I P y).trans h)
  have hd := globalSupportParameterDivisor_dimension I P (P.subschemeι ≫ f)
    (Support.Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P y) hy
  have ha := Point.SupportDimension.BundleCycles.pointClosure_dimension_closedImmersion (Support.Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P)
    (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P ≫ (P.subschemeι ≫ f)) y
  have hb := Point.SupportDimension.BundleCycles.pointClosure_dimension_closedImmersion (Support.Specialization.BundleCycles.globalSupportSpecialFiberMap I P)
    (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) y
  have hs : Support.Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P ≫
      (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P ≫ (P.subschemeι ≫ f)) =
      Support.Specialization.BundleCycles.globalSupportSpecialFiberMap I P ≫ (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) := by
    rw [← Category.assoc (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P), ← Category.assoc,
      globalSupportSpecialFiber_toBase, Category.assoc]
  exact hb.trans ((congrArg
    (fun g => Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) g) hs.symm).trans
    (ha.symm.trans hd))

omit [IsIntegral P.subscheme] in
/-- The global prime specialization preserves the dimension of the actual reduced point closure. -/
theorem globalPrimeSpecialization_dimension
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (x : X) (y : Global.SpecialFiber.BundleCycles.globalSpecialFiber I) (hy : Global.CycleSpecialization.BundleCycles.globalPrimeSpecialization I x y ≠ 0) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y)
        (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f :=
  globalClosedSupportSpecialization_dimension I
    (CycleClass.Geometric.GenericPoint.reducedSupportIdeal (irreducibleSetEquivPoints.symm x)) f y hy

omit [IsIntegral P.subscheme] in
theorem globalPrimeSpecializationQ_dimension
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (x : X) (y : Global.SpecialFiber.BundleCycles.globalSpecialFiber I) (hy : Global.CycleSpecialization.BundleCycles.globalPrimeSpecializationQ I x y ≠ 0) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y)
        (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f := by
  apply globalPrimeSpecialization_dimension I f x y
  intro h
  apply hy
  change (Global.CycleSpecialization.BundleCycles.globalPrimeSpecialization I x y : ℚ) = 0
  exact (congrArg (fun z : ℤ => (z : ℚ)) h).trans Int.cast_zero

end

/-! Nonzero specialization coefficients lie over specializations of
the original generic support point in the ambient scheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] (I : X.IdealSheafData)

theorem globalClosedSupportSpecialization_support_base (P : X.IdealSheafData) [IsIntegral P.subscheme]
    (y : Global.SpecialFiber.BundleCycles.globalSpecialFiber I) (hy : Support.Specialization.BundleCycles.globalClosedSupportSpecialization I P y ≠ 0) :
    Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I y ∈ Set.range P.subschemeι := by
  have hr : y ∈ Set.range (Support.Specialization.BundleCycles.globalSupportSpecialFiberMap I P) := by
    by_contra hn
    exact hy (Finsupp.embDomain_of_notMem_range _ _ _ hn)
  obtain ⟨v, rfl⟩ := hr
  refine ⟨Support.Projection.BundleCycles.globalSupportDeformationToSupport I P (Support.Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P v), ?_⟩
  exact congrArg (fun a : Support.Specialization.BundleCycles.globalSupportSpecialFiber I P ⟶ X => a v) (globalSupportSpecialFiber_toBase I P)

theorem globalPrimeSpecialization_specializes (x : X) (y : Global.SpecialFiber.BundleCycles.globalSpecialFiber I)
    (hy : Global.CycleSpecialization.BundleCycles.globalPrimeSpecialization I x y ≠ 0) : x ⤳ Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I y := by
  have H := globalClosedSupportSpecialization_support_base I
    (CycleClass.Geometric.GenericPoint.reducedSupportIdeal (irreducibleSetEquivPoints.symm x)) y hy
  change Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I y ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) at H
  rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι] at H
  exact specializes_iff_mem_closure.mpr H

theorem globalPrimeSpecializationQ_specializes (x : X) (y : Global.SpecialFiber.BundleCycles.globalSpecialFiber I)
    (hy : Global.CycleSpecialization.BundleCycles.globalPrimeSpecializationQ I x y ≠ 0) : x ⤳ Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I y := by
  apply globalPrimeSpecialization_specializes I x y
  intro hz
  apply hy
  change (Global.CycleSpecialization.BundleCycles.globalPrimeSpecialization I x y : ℚ) = 0
  rw [hz, Int.cast_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalSpecializationGrading.BundleCycles
