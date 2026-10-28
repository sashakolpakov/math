import OAI.AlgebraicGeometry.Divisors.LineBundles.DVRAbsoluteValue
import OAI.AlgebraicGeometry.Divisors.LineBundles.FractionOrderLaws
import OAI.AlgebraicGeometry.Divisors.LineBundles.DVRMultiplicity

/-! # DVR Approximation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.DVRApproximation.BundleCycles

noncomputable section

/-! Weak approximation prescribes the actual DVR orders in a finite
family with inequivalent absolute values. -/

open scoped _root_.Topology

variable {ι : Type*} [Finite ι] (A : ι → Type*) (K : Type*)
    [∀ i, CommRing (A i)] [∀ i, IsDomain (A i)] [∀ i, IsDiscreteValuationRing (A i)]
    [Field K] [∀ i, Algebra (A i) K] [∀ i, IsFractionRing (A i) K]
    (hne : Pairwise fun i j => ¬ (DVRAbsoluteValue.BundleCycles.dvrAbsoluteValue (A i) K).IsEquiv (DVRAbsoluteValue.BundleCycles.dvrAbsoluteValue (A j) K))

include hne in
theorem exists_finiteDVR_same_values (t : ι → K) (ht : ∀ i, t i ≠ 0) :
    ∃ a : K, ∀ i, (IsDiscreteValuationRing.maximalIdeal (A i)).valuation K a =
      (IsDiscreteValuationRing.maximalIdeal (A i)).valuation K (t i) := by
  let v := fun i => DVRAbsoluteValue.BundleCycles.dvrAbsoluteValue (A i) K
  let z : ∀ i, WithAbs (v i) := fun i => (WithAbs.equiv (v i)).symm (t i)
  let B := Set.univ.pi (fun i => Metric.ball (z i) (v i (t i)))
  have hB : IsOpen B := isOpen_set_pi Set.finite_univ (fun _ _ => Metric.isOpen_ball)
  have hz : z ∈ B := by
    intro i _
    exact Metric.mem_ball.mpr (by simpa only [dist_self] using (v i).pos (ht i))
  have hd := AbsoluteValue.denseRange_algebraMap_pi (fun i => DVRAbsoluteValue.BundleCycles.dvrAbsoluteValue_nontrivial (A i) K) hne
  obtain ⟨a, ha⟩ := hd.exists_mem_open hB ⟨z, hz⟩
  refine ⟨a, fun i => ?_⟩
  have hi := Metric.mem_ball.mp (ha i (Set.mem_univ i))
  have hdist : v i (a - t i) < v i (t i) := by
    rw [dist_eq_norm] at hi
    exact hi
  exact ((IsDiscreteValuationRing.maximalIdeal (A i)).valuation K).map_eq_of_sub_lt
    ((DVRAbsoluteValue.BundleCycles.dvrAbsoluteValue_lt_iff (A i) K (a - t i) (t i)).mp hdist)

include hne in
theorem exists_finiteDVR_prescribed_orders (n : ι → ℤ) :
    ∃ a : Kˣ, ∀ i, SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder (A i) (a : K) = n i := by
  classical
  by_cases hι : Nonempty ι
  · let := hι
    choose π hπ using fun i => IsDiscreteValuationRing.exists_irreducible (A i)
    let t : ι → K := fun i => (algebraMap (A i) K (π i)) ^ n i
    have ht : ∀ i, t i ≠ 0 := by
      intro i
      apply zpow_ne_zero
      simpa only [map_zero] using (IsFractionRing.injective (A i) K).ne (hπ i).ne_zero
    obtain ⟨a, ha⟩ := exists_finiteDVR_same_values A K hne t ht
    have ha0 : a ≠ 0 := by
      intro hz
      let i := Classical.choice hι
      have he := ha i
      rw [hz, map_zero] at he
      exact ((map_ne_zero ((IsDiscreteValuationRing.maximalIdeal (A i)).valuation K)).mpr (ht i)) he.symm
    refine ⟨Units.mk0 a ha0, fun i => ?_⟩
    have he : Ring.ordFrac (A i) a = Ring.ordFrac (A i) (t i) := by
      rw [Ring.ordFrac_eq_valuation_inv, Ring.ordFrac_eq_valuation_inv, ha i]
    have htord := DVRMultiplicity.BundleCycles.ordFrac_unit_zpow (K := K) (π i) (hπ i) (1 : (A i)ˣ) (n i)
    rw [one_smul] at htord
    change Multiplicative.toAdd ((Ring.ordFrac (A i) a).unzeroD 1) = n i
    rw [he, htord]
    rfl
  · let : IsEmpty ι := not_nonempty_iff.mp hι
    exact ⟨1, fun i => isEmptyElim i⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.DVRApproximation.BundleCycles
