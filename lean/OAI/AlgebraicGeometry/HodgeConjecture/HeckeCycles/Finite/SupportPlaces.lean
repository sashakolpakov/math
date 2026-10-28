import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlaceAt

/-! # Support Places -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SupportPlaces.CM

noncomputable section

/-! Compact sets of finite-adelic positions are integral outside one
finite set of places, uniformly over every position in the set. -/

open scoped Classical
open Filter
variable {I : Type*} [Fintype I]

theorem compact_eventually_integral (K : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (hK : IsCompact K) :
    ∀ᶠ v in cofinite, ∀ x ∈ K, ∀ i, x i v ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨n, hn, hbound⟩ := RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.compact_subset_integralBox K hK
  let a := algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (n : ℚ)⁻¹
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have ha : a * (n : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) = 1 := by
    change algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (n : ℚ)⁻¹ * (n : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) = 1
    rw [← map_intCast (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) n, ← map_mul, inv_mul_cancel₀ hnq, map_one]
  filter_upwards [a.property] with v hv
  intro x hx i
  have h := (v.adicCompletionIntegers ℚ).mul_mem _ _ hv (hbound hx i v)
  have he : a * ((n : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) * x i) = x i := by rw [← mul_assoc, ha, one_mul]
  change (a * ((n : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) * x i)) v ∈ v.adicCompletionIntegers ℚ at h
  rwa [he] at h

theorem compact_integral_outside (K : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (hK : IsCompact K) :
    ∃ S : Finset RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, ∀ T : Finset RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, S ⊆ T →
      ∀ x ∈ K, ∀ i v, v ∉ T → x i v ∈ v.adicCompletionIntegers ℚ := by
  have hbad : {v | ¬∀ x ∈ K, ∀ i, x i v ∈ v.adicCompletionIntegers ℚ}.Finite :=
    compact_eventually_integral K hK
  refine ⟨hbad.toFinset, ?_⟩
  intro T hT x hx i v hv
  have hvS : v ∉ hbad.toFinset := fun h => hv (hT h)
  have hg : ∀ x ∈ K, ∀ i, x i v ∈ v.adicCompletionIntegers ℚ := by
    simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hvS
  exact hg x hx i

theorem test_support_integral_outside (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    ∃ S : Finset RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, ∀ T : Finset RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, S ⊆ T →
      ∀ x ∈ tsupport f.val, ∀ i v, v ∉ T → x i v ∈ v.adicCompletionIntegers ℚ :=
  compact_integral_outside (tsupport f.val) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_hasCompactSupport f)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SupportPlaces.CM
