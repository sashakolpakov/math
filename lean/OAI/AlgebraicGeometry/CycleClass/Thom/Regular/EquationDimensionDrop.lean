import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.SequenceTailChange
import OAI.AlgebraicGeometry.CycleClass.Thom.PrimeAvoidanceCoset
import Mathlib.RingTheory.KrullDimension.Regular

/-! # Equation Dimension Drop -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Regular.EquationDimensionDrop.Constructions

noncomputable section

/-! At an isolated intersection with a positive-dimensional module,
regular ambient equations admit a first equation avoiding every minimal
source prime. The generated ideal stays fixed and source dimension drops. -/

open RingTheory.Sequence
open scoped Pointwise

open OAI.AlgebraicGeometry.CycleClass.Thom.Regular.SequenceTailChange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.PrimeAvoidanceCoset.Constructions

universe u v w
variable {R : Type u} [CommRing R] [IsLocalRing R]
  (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N]

theorem minimalPrime_ne_maximalIdeal (P : Ideal R)
    (hP : P ∈ (Module.annihilator R N).minimalPrimes)
    (hd : 0 < Module.supportDim R N) : P ≠ IsLocalRing.maximalIdeal R := by
  intro hPm
  have he (q : Module.support R N) : q.val.asIdeal = P := by
    have hle : q.val.asIdeal ≤ P := hPm ▸ IsLocalRing.le_maximalIdeal q.val.isPrime.ne_top
    exact le_antisymm hle (hP.2 ⟨q.val.isPrime, Module.mem_support_iff_of_finite.mp q.property⟩ hle)
  let : Subsingleton (Module.support R N) := ⟨fun q r =>
    Subtype.ext (PrimeSpectrum.ext ((he q).trans (he r).symm))⟩
  have hz : Module.supportDim R N ≤ 0 := Order.krullDim_nonpos_of_subsingleton
  exact (not_lt_of_ge hz) hd

theorem isolated_ideal_not_le_minimalPrime (I P : Ideal R)
    (hP : P ∈ (Module.annihilator R N).minimalPrimes)
    (hd : 0 < Module.supportDim R N)
    (hi : PrimeSpectrum.zeroLocus (I : Set R) ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R}) :
    ¬ I ≤ P := by
  intro hIP
  let q : PrimeSpectrum R := ⟨P, hP.isPrime⟩
  have hq : q ∈ PrimeSpectrum.zeroLocus (I : Set R) ∩ Module.support R N :=
    ⟨hIP, Module.mem_support_iff_of_finite.mpr hP.le⟩
  have he : q = IsLocalRing.closedPoint R := Set.mem_singleton_iff.mp (hi hq)
  exact minimalPrime_ne_maximalIdeal N P hP hd (congrArg PrimeSpectrum.asIdeal he)

variable [IsNoetherianRing R]
  (M : Type w) [AddCommGroup M] [Module R M] [IsNoetherian R M]

theorem exists_regular_head_dimension_drop (x : R) (rs : List R)
    (hr : IsWeaklyRegular M (x :: rs))
    (hm : ∀ r ∈ x :: rs, r ∈ IsLocalRing.maximalIdeal R)
    (hd : 0 < Module.supportDim R N)
    (hi : PrimeSpectrum.zeroLocus (Ideal.ofList (x :: rs) : Set R) ∩ Module.support R N ⊆
      {IsLocalRing.closedPoint R}) :
    ∃ t ∈ Ideal.ofList rs,
      Ideal.ofList ((x + t) :: rs) = Ideal.ofList (x :: rs) ∧
      IsWeaklyRegular M ((x + t) :: rs) ∧
      (∀ P ∈ (Module.annihilator R N).minimalPrimes, x + t ∉ P) ∧
      Module.supportDim R (QuotSMulTop (x + t) N) + 1 ≤ Module.supportDim R N := by
  classical
  let s := (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Module.annihilator R N)).toFinset
  have hs (P : Ideal R) : P ∈ s ↔ P ∈ (Module.annihilator R N).minimalPrimes :=
    Set.Finite.mem_toFinset _
  have hp (P : Ideal R) (hP : P ∈ s) : P.IsPrime := ((hs P).mp hP).isPrime
  have ha (P : Ideal R) (hP : P ∈ s) (Q : Ideal R) (hQ : Q ∈ s) (hle : P ≤ Q) : P = Q :=
    le_antisymm hle (((hs Q).mp hQ).2 ((hs P).mp hP).1 hle)
  have hI (P : Ideal R) (hP : P ∈ s) : ¬ Ideal.span {x} ⊔ Ideal.ofList rs ≤ P := by
    rw [← Ideal.ofList_cons]
    exact isolated_ideal_not_le_minimalPrime N _ P ((hs P).mp hP) hd hi
  obtain ⟨t, ht, hav⟩ := PrimeAvoidanceCoset.Constructions.exists_add_avoiding s hp ha (Ideal.ofList rs) x hI
  have hav' : ∀ P ∈ (Module.annihilator R N).minimalPrimes, x + t ∉ P :=
    fun P hP => hav P ((hs P).mpr hP)
  exact ⟨t, ht, SequenceTailChange.Constructions.ofList_add_tail x t rs ht, SequenceTailChange.Constructions.weaklyRegular_add_tail M x t rs ht hm hr, hav',
    Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes hav'⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Regular.EquationDimensionDrop.Constructions
