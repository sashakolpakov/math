import OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceProperCriterion
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # Auxiliary Parameter -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.AuxiliaryParameter.BundleCycles

noncomputable section

/-!
# LineBundleCycles: an actual auxiliary annihilator transverse to a branch equation

Prime avoidance selects an element of an ideal with radical P which
avoids all minimal primes of x, provided x is outside P. On a local
surface, this gives a proper parameter pair (x,y), with y in the
original ideal. It permits reuse of the proved two-equation filtration
formula for a module supported on the single branch P.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem minimalPrincipalPrimes_comparable_eq (r s : R) (hr : r ≠ 0)
    (P Q : Ideal R) (hP : P ∈ (Ideal.span {r}).minimalPrimes)
    (hQ : Q ∈ (Ideal.span {s}).minimalPrimes) (hpq : P ≤ Q) : P = Q := by
  let auxiliaryFirstPrime : P.IsPrime := hP.isPrime
  let auxiliarySecondPrime : Q.IsPrime := hQ.isPrime
  have hPbot : P ≠ ⊥ := by
    intro he
    have hp := hP.le (Ideal.subset_span (Set.mem_singleton r))
    rw [he, Ideal.mem_bot] at hp
    exact hr hp
  have hPheight : (1 : ℕ∞) ≤ P.height :=
    Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hPbot)
  by_contra hne
  have hQheight : (2 : ℕ∞) ≤ Q.height :=
    (add_le_add hPheight (le_refl (1 : ℕ∞))).trans
      (Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hpq hne))
  have hQone : Q.height ≤ (1 : ℕ∞) :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {s}) Q hQ
  exact (by norm_num : ¬ (2 : ℕ∞) ≤ 1) (hQheight.trans hQone)

theorem branchIdeal_exists_avoiding_equation (r x : R) (hr : r ≠ 0)
    (P I : Ideal R) (hP : P ∈ (Ideal.span {r}).minimalPrimes)
    (hI : I.radical = P) (hxP : x ∉ P) :
    ∃ y ∈ I, ∀ Q : Ideal R, Q ∈ (Ideal.span {x}).minimalPrimes → y ∉ Q := by
  classical
  let S := (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {x})).toFinset
  have hnot : ¬ (I : Set R) ⊆ ⋃ Q ∈ (S : Set (Ideal R)), (Q : Set R) := by
    intro hi
    obtain ⟨Q, hQS, hIQ⟩ := (Ideal.subset_union_prime (s := S) (f := fun Q : Ideal R => Q)
      (⊥ : Ideal R) (⊥ : Ideal R) (fun Q hQS _ _ => by
        exact ((Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {x})).mem_toFinset.mp hQS).isPrime)).mp hi
    have hQ : Q ∈ (Ideal.span {x}).minimalPrimes :=
      (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {x})).mem_toFinset.mp hQS
    have hpq : P ≤ Q := hI ▸ hQ.isPrime.radical_le_iff.mpr hIQ
    have he := minimalPrincipalPrimes_comparable_eq r x hr P Q hP hQ hpq
    exact hxP (he.symm ▸ hQ.le (Ideal.subset_span (Set.mem_singleton x)))
  obtain ⟨y, hyI, hy⟩ := Set.not_subset.mp hnot
  refine ⟨y, hyI, ?_⟩
  intro Q hQ hyQ
  apply hy
  exact Set.mem_iUnion₂.mpr ⟨Q,
    (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {x})).mem_toFinset.mpr hQ, hyQ⟩

omit [IsDomain R] in
theorem minimalPrincipalPrime_ne_maximal [IsLocalRing R]
    (r : R) (hdim : ringKrullDim R = 2) (P : Ideal R)
    (hP : P ∈ (Ideal.span {r}).minimalPrimes) : P ≠ IsLocalRing.maximalIdeal R := by
  intro he
  have hh : P.height ≤ (1 : ℕ∞) :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {r}) P hP
  have hm : ((IsLocalRing.maximalIdeal R).height : WithBot ℕ∞) ≤ 1 :=
    WithBot.coe_le_coe.mpr (he ▸ hh)
  rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdim] at hm
  exact (by norm_num : ¬ (2 : WithBot ℕ∞) ≤ 1) hm

theorem branchIdeal_exists_proper_parameter [IsLocalRing R]
    (r x : R) (hr : r ≠ 0) (hdim : ringKrullDim R = 2)
    (P I : Ideal R) (hP : P ∈ (Ideal.span {r}).minimalPrimes)
    (hI : I.radical = P) (hxP : x ∉ P) (hxunit : ¬ IsUnit x) :
    ∃ y ∈ I, y ≠ 0 ∧ (Ideal.span {x, y}).radical = IsLocalRing.maximalIdeal R := by
  obtain ⟨y, hyI, hy⟩ := branchIdeal_exists_avoiding_equation r x hr P I hP hI hxP
  have hx : x ≠ 0 := fun he => hxP (he ▸ P.zero_mem)
  have hIproper : I ≠ ⊤ := by
    intro he
    have ht : P = ⊤ := hI.symm.trans (by rw [he, Ideal.radical_top])
    exact hP.isPrime.ne_top ht
  have hyunit : ¬ IsUnit y := fun hu => hIproper (Ideal.eq_top_of_isUnit_mem I hyI hu)
  have hxmax : Ideal.span {x} ≤ IsLocalRing.maximalIdeal R :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxunit)
  obtain ⟨Q, hQ, _⟩ := Ideal.exists_minimalPrimes_le hxmax
  have hyzero : y ≠ 0 := fun he => hy Q hQ (he ▸ Q.zero_mem)
  refine ⟨y, hyI, hyzero, ?_⟩
  rw [Set.pair_comm x y]
  exact SurfaceProperCriterion.BundleCycles.surfaceProperPair_radical y x hx hdim hyunit hxunit hy

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.AuxiliaryParameter.BundleCycles
