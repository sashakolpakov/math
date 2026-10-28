import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PointRelation
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.CycleGrading

/-! # Relation Grading -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.RelationGrading.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual horizontal point relations preserve the exact Chow dimension grade -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem affineLineNonextendedPoint_graded_relation (d : ℕ)
    (y : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1))
    (hy : y.val ∉ Set.range (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X))) :
    ∃ (W : IrreducibleCloseds (Charts.BundleCycles.affineLine X)) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField),
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W (Charts.BundleCycles.affineLineProjection X ≫ f) = (d + 1) + 1 ∧ g ≠ 0 ∧
      ∃ z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ,
        Finsupp.single y 1 + CycleGrading.BundleCycles.affineLineGradedCycleExtension X f d z =
          Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) W g := by
  obtain ⟨W, g, hg, w, hrel⟩ := PointRelation.BundleCycles.affineLineNonextendedPoint_cycle_relation X y.val hy
  have hcoeff : Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g y.val = 1 := by
    have h := congrArg (fun z : Charts.BundleCycles.affineLine X →₀ ℚ => z y.val) hrel
    change Finsupp.single y.val (1 : ℚ) y.val +
      Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) w y.val = _ at h
    rw [Finsupp.single_eq_same, Finsupp.mapDomain_of_notMem_range _ _ hy, add_zero] at h
    exact h.symm
  have hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W (Charts.BundleCycles.affineLineProjection X ≫ f) = (d + 1) + 1 := by
    have h := Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_dimension (Charts.BundleCycles.affineLineProjection X ≫ f) W g y.val
      (hcoeff ▸ one_ne_zero)
    exact h.symm.trans (congrArg (fun n => n + 1) y.property)
  have hs : (w.support : Set X) ⊆ Set.range (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) := by
    intro x hx
    have hxzero : w x ≠ 0 := Finsupp.mem_support_iff.mp hx
    have hneq : Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x ≠ y.val := fun h => hy ⟨x, h⟩
    have h := congrArg (fun z : Charts.BundleCycles.affineLine X →₀ ℚ => z (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x)) hrel
    change Finsupp.single y.val (1 : ℚ) (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x) +
      Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) w
        (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x) = _ at h
    rw [Finsupp.single_eq_of_ne hneq, Finsupp.mapDomain_apply_of_injective (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_injective (Charts.BundleCycles.affineLineProjection X)), zero_add] at h
    have hn : Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x) ≠ 0 :=
      fun hz => hxzero (h.trans hz)
    have hd := Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_dimension (Charts.BundleCycles.affineLineProjection X ≫ f) W g _ hn
    rw [CycleGrading.BundleCycles.affineLineFiberGenericPoint_dimension, hW] at hd
    refine ⟨⟨x, ?_⟩, rfl⟩
    omega
  let z := Finsupp.comapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) w (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d).injective.injOn
  have hz : Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z = w :=
    Finsupp.mapDomain_comapDomain _ (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d).injective w hs
  refine ⟨W, g, hW, hg, z, ?_⟩
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)
  rw [map_add, CycleGrading.BundleCycles.affineLineGradedCycleExtension_forget, hz,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) W hW]
  have hi : Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) (Finsupp.single y 1) =
      Finsupp.single y.val 1 := Finsupp.mapDomain_single
  rw [hi]
  exact hrel

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.RelationGrading.BundleCycles
