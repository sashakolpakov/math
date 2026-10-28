import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialProducts
import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.IntrinsicStep
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialOrderBound

/-! # Differential Saturation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialSaturation.Construction

noncomputable section

/-! Intrinsic differential saturation: a canonical ideal detecting identically vanishing components. -/

section

universe u

variable (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R]

def relativeDifferentialSaturation (J : Ideal R) : Ideal R :=
  ⨆ n : ℕ, Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n

theorem le_relativeDifferentialSaturation (J : Ideal R) : J ≤ relativeDifferentialSaturation k J :=
  le_iSup (fun n => Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) 0

theorem relativeDifferentialSaturation_top : relativeDifferentialSaturation k (⊤ : Ideal R) = ⊤ :=
  top_le_iff.mp (le_relativeDifferentialSaturation k ⊤)

theorem firstRelativeDifferentialIdeal_bot : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (⊥ : Ideal R) = ⊥ := by
  apply le_bot_iff.mp
  apply sup_le bot_le
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨D, p⟩, rfl⟩
  have hp : p.val = 0 := p.property
  change D p.val ∈ (⊥ : Ideal R)
  rw [hp, map_zero]
  exact Ideal.zero_mem _

theorem iteratedRelativeDifferentialIdeal_bot (n : ℕ) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (⊥ : Ideal R) n = ⊥ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal, firstRelativeDifferentialIdeal_bot]
      exact ih

theorem relativeDifferentialSaturation_bot : relativeDifferentialSaturation k (⊥ : Ideal R) = ⊥ := by
  simp only [relativeDifferentialSaturation, iteratedRelativeDifferentialIdeal_bot, iSup_const]

theorem relativeDifferentialSaturation_eq_top_of_bound (J : Ideal R) (n : ℕ)
    (h : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n = ⊤) : relativeDifferentialSaturation k J = ⊤ := by
  apply top_le_iff.mp
  rw [← h]
  exact le_iSup (fun m => Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J m) n

theorem first_relativeDifferentialSaturation (J : Ideal R) :
    Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (relativeDifferentialSaturation k J) = relativeDifferentialSaturation k J := by
  apply le_antisymm
  · rw [relativeDifferentialSaturation, Relative.DifferentialProducts.Construction.firstRelativeDifferentialIdeal_iSup]
    apply iSup_le
    intro n
    rw [Curve.IntrinsicStep.Construction.first_iteratedRelativeDifferentialIdeal]
    exact le_iSup (fun m => Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J m) (n + 1)
  · exact Relative.DifferentialBlowup.Construction.le_firstRelativeDifferentialIdeal k _

theorem relativeDifferentialSaturation_eq_iterate [IsNoetherianRing R] (J : Ideal R) :
    ∃ n : ℕ, relativeDifferentialSaturation k J = Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n := by
  let F : ℕ →o Submodule R R :=
    ⟨Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J, Coefficient.UnitCriterion.Construction.iteratedRelativeDifferentialIdeal_monotone_order k J⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance F
  refine ⟨n, le_antisymm ?_ (le_iSup (fun m => Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J m) n)⟩
  apply iSup_le
  intro m
  by_cases hm : m ≤ n
  · exact Coefficient.UnitCriterion.Construction.iteratedRelativeDifferentialIdeal_monotone_order k J hm
  · exact (hn m (by omega)).symm.le

theorem relativeDifferentialSaturation_map {S : Type u} [CommRing S] [Algebra k S]
    [Algebra.Smooth k R] (f : R →ₐ[k] S) (hf : f.toRingHom.Etale) (J : Ideal R) :
    (relativeDifferentialSaturation k J).map f.toRingHom =
      relativeDifferentialSaturation k (J.map f.toRingHom) := by
  simp only [relativeDifferentialSaturation, Ideal.map_iSup,
    Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hf]

end

universe u

variable (k : Type u) {R : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]

theorem relativeDifferentialSaturation_eq_top_of_ne_bot (J : Ideal R) (hJ : J ≠ ⊥) :
    relativeDifferentialSaturation k J = ⊤ := by
  obtain ⟨n, hn⟩ := Blowups.Smooth.DifferentialOrderBound.Construction.exists_smooth_relative_differential_order_bound k J hJ
  exact relativeDifferentialSaturation_eq_top_of_bound k J n hn

theorem relativeDifferentialSaturation_domain_dichotomy (J : Ideal R) :
    relativeDifferentialSaturation k J = ⊥ ∨ relativeDifferentialSaturation k J = ⊤ := by
  by_cases hJ : J = ⊥
  · left
    rw [hJ]
    exact relativeDifferentialSaturation_bot k (R := R)
  · exact Or.inr (relativeDifferentialSaturation_eq_top_of_ne_bot k J hJ)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialSaturation.Construction
