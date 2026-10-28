import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.DimensionBound
import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.PointResidue
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PrincipalRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportNaturality

/-! # Residue Support Coheight -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ResidueSupportCoheight.BundleCycles

noncomputable section

/-!
# LineBundleCycles: geometric residue divisors are supported in ambient coheight two

The support dimension drops twice. The general chain-length bound
gives coheight at most two, while the strict specialization from a
divisor generic point gives coheight at least two.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

theorem schemeGenericPoint_coheight_zero (A : Scheme) [IsIntegral A] : coheight (genericPoint A) = 0 := by
  apply coheight_eq_zero.mpr
  intro y _
  exact Scheme.le_iff_specializes.mpr ((genericPoint_spec A).specializes trivial)

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

omit [IsIntegral X] in
theorem primeSupport_divisor_coheight_ge_two (x : X) (hx : coheight x = 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField)
    (y : X) (hy : Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x) g y ≠ 0) :
    2 ≤ coheight y := by
  let W := irreducibleSetEquivPoints.symm x
  have hyr : y ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι W) := by
    by_contra hn
    apply hy
    exact Finsupp.embDomain_of_notMem_range _ _ _ hn
  obtain ⟨z, rfl⟩ := hyr
  have hz : coheight z = 1 := by
    by_contra hn
    apply hy
    rw [Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_at_support, Scheme.ord_eq_zero_of_coheight_neq_one hn, Int.cast_zero]
  have hne : CycleClass.Geometric.GenericPoint.reducedSupportι W z ≠ x := by
    intro he
    have he' : z = genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) :=
      (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective (he.trans (Point.SupportNaturality.BundleCycles.pointSupport_genericPoint X x).symm)
    rw [he', schemeGenericPoint_coheight_zero] at hz
    exact (by decide : (0 : ℕ∞) ≠ 1) hz
  have hle : CycleClass.Geometric.GenericPoint.reducedSupportι W z ≤ x := by
    apply Scheme.le_iff_specializes.mpr
    apply specializes_iff_mem_closure.mpr
    exact (congrArg (fun S : Set X => CycleClass.Geometric.GenericPoint.reducedSupportι W z ∈ S) (CycleClass.Geometric.GenericPoint.range_reducedSupportι W)).mp ⟨z, rfl⟩
  have hn : ¬ x ≤ CycleClass.Geometric.GenericPoint.reducedSupportι W z := by
    intro hr
    exact hne (Inseparable.eq (Specializes.antisymm
      (Scheme.le_iff_specializes.mp hr) (Scheme.le_iff_specializes.mp hle)))
  have hb := coheight_add_one_le (lt_of_le_not_ge hle hn)
  norm_num only [hx] at hb
  exact hb

theorem primeSupport_divisor_coheight_two (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (x : X) (hx : coheight x = 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField)
    (y : X) (hy : Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x) g y ≠ 0) :
    coheight y = 2 := by
  have hlow := primeSupport_divisor_coheight_ge_two x hx g y hy
  have hD := Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_dimension f (irreducibleSetEquivPoints.symm x) g y hy
  have hX := DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one f x hx
  have hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) f + 2 =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by omega
  have hbound := Point.DimensionBound.BundleCycles.coheight_add_pointDimension_le f y
  rw [← hdim, Nat.cast_add, Nat.cast_ofNat] at hbound
  have hu : coheight y ≤ 2 :=
    (ENat.add_le_add_iff_right
      (k := (Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) f : ℕ∞))
      (by simp)).mp (hbound.trans_eq (add_comm _ _))
  exact le_antisymm hu hlow

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ResidueSupportCoheight.BundleCycles
