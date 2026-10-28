import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ClosedOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialOrderLocus
import OAI.AlgebraicGeometry.Resolution.Blowups.Ideal.Order

/-! # Order Bound -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.OrderBound.Construction

noncomputable section

/-! A uniform finite order bound for arbitrary nonzero ideals on integral étale coordinate neighborhoods. -/

variable {σ K S : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [Fintype σ] [DecidableEq σ] [CommRing S] [IsDomain S]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

include σ K

/-- On an integral étale polynomial algebra, iterated differentiation of
any nonzero ideal eventually produces the unit ideal. The proof uses
Noetherian stabilization and Krull intersection in a local ring. -/
theorem exists_etale_differential_order_bound (J : Ideal S) (hJ : J ≠ ⊥) :
    ∃ n : ℕ, DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J n = ⊤ := by
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing (MvPolynomial σ K) S
  let F : ℕ →o Submodule S S :=
    ⟨DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J, DifferentialOrderLocus.Construction.iteratedDifferentialIdeal_monotone J⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance F
  refine ⟨n, ?_⟩
  by_contra hproper
  obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J n) hproper
  let : q.IsMaximal := hq
  have hall : ∀ b, DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J b ≤ q := by
    intro b
    by_cases hb : b ≤ n
    · exact (DifferentialOrderLocus.Construction.iteratedDifferentialIdeal_monotone J hb).trans hle
    · have he : DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J n = DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J b :=
        hn b (by omega)
      rwa [← he]
  let T := Localization.AtPrime q
  let M := IsLocalRing.maximalIdeal T
  have hlocal : J.map (algebraMap S T) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hJ
  obtain ⟨b, _, hb⟩ := Blowups.Ideal.Order.Construction.exists_idealAdicOrder M (J.map (algebraMap S T))
    (IsLocalRing.maximalIdeal.isMaximal T).ne_top hlocal
  exact hb ((ClosedOrder.Construction.etale_closedPoint_order_iff_differentialIdeal (σ := σ) (K := K) J q b).mpr (hall b))

/-- The same natural number bounds the order at every closed point. -/
theorem exists_etale_uniform_order_bound (J : Ideal S) (hJ : J ≠ ⊥) :
    ∃ n : ℕ, ∀ (q : Ideal S) [q.IsMaximal],
      ¬ J.map (algebraMap S (Localization.AtPrime q)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (n + 1) := by
  obtain ⟨n, hn⟩ := exists_etale_differential_order_bound (σ := σ) (K := K) J hJ
  refine ⟨n, ?_⟩
  intro q hq horder
  have h := (ClosedOrder.Construction.etale_closedPoint_order_iff_differentialIdeal (σ := σ) (K := K) J q n).mp horder
  rw [hn] at h
  exact hq.ne_top (top_le_iff.mp h)

/-- A nonzero ideal attains its finite maximum local order at a closed
point of the integral étale neighborhood. -/
theorem exists_etale_maximum_order (J : Ideal S) (hJ : J ≠ ⊥) :
    ∃ (b : ℕ) (q : Ideal S) (_ : q.IsMaximal),
      J.map (algebraMap S (Localization.AtPrime q)) ≤
          IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ b ∧
        ∀ (p : Ideal S) [p.IsMaximal],
          ¬ J.map (algebraMap S (Localization.AtPrime p)) ≤
            IsLocalRing.maximalIdeal (Localization.AtPrime p) ^ (b + 1) := by
  classical
  obtain ⟨n, hn⟩ := exists_etale_uniform_order_bound (σ := σ) (K := K) J hJ
  let P : ℕ → Prop := fun b => ∀ (q : Ideal S) [q.IsMaximal],
    ¬ J.map (algebraMap S (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ b
  have hex : ∃ b, P b := ⟨n + 1, hn⟩
  have hm0 : Nat.find hex ≠ 0 := by
    intro hz
    obtain ⟨q, hq⟩ := Ideal.exists_maximal S
    let : q.IsMaximal := hq
    have h := Nat.find_spec hex q
    rw [hz, pow_zero, Ideal.one_eq_top] at h
    exact h le_top
  obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hnot : ¬ P b := by
    intro h
    have hmin := Nat.find_min' hex h
    omega
  change ¬ ∀ (q : Ideal S) (hq : q.IsMaximal),
    ¬ J.map (algebraMap S (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ b at hnot
  push Not at hnot
  obtain ⟨q, hq, horder⟩ := hnot
  refine ⟨b, q, hq, horder, ?_⟩
  simpa only [hb, Nat.succ_eq_add_one] using Nat.find_spec hex

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.OrderBound.Construction
