import OAI.AlgebraicGeometry.Divisors.LineBundles.SurfacePrimeFactors

/-! # Surface Proper Criterion -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceProperCriterion.BundleCycles

noncomputable section

/-!
# LineBundleCycles: proper prime-support separation gives the actual local parameter condition

If two nonunits have no common minimal prime component on a local
surface, every prime containing both is maximal. Their generated ideal
therefore has the maximal ideal as its radical, as required by the
proved local intersection formula.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem surfaceProperPair_radical (a b : R) (hb : b ≠ 0) (hdim : ringKrullDim R = 2)
    (haunit : ¬ IsUnit a) (hbunit : ¬ IsUnit b)
    (hproper : ∀ P : Ideal R, P ∈ (Ideal.span {b}).minimalPrimes → a ∉ P) :
    (Ideal.span {a, b}).radical = IsLocalRing.maximalIdeal R := by
  let : Ring.KrullDimLE 2 R := Ring.krullDimLE_iff.mpr hdim.le
  have hI : Ideal.span {a, b} ≤ IsLocalRing.maximalIdeal R := by
    apply Ideal.span_le.mpr
    intro t ht
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · exact haunit
    · exact (Set.mem_singleton_iff.mp ht) ▸ hbunit
  apply le_antisymm
  · exact (Ideal.radical_mono hI).trans_eq (inferInstance : (IsLocalRing.maximalIdeal R).IsPrime).radical
  · rw [Ideal.radical_eq_sInf]
    apply le_sInf
    intro P hP
    let : P.IsPrime := hP.2
    have haP : a ∈ P := hP.1 (Ideal.subset_span (Set.mem_insert a {b}))
    have hbP : b ∈ P := hP.1 (Ideal.subset_span (Set.mem_insert_of_mem a (Set.mem_singleton b)))
    rcases SurfacePrimeFactors.BundleCycles.surfacePrime_minimal_or_maximal b hb P hbP with hmin | he
    · exact False.elim (hproper P hmin haP)
    · exact he.symm.le

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceProperCriterion.BundleCycles
