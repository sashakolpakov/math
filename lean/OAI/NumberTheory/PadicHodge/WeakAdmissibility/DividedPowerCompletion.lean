import OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaDividedPowers
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.BoundedCompletion

/-! # Divided Power Completion -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.DividedPowerCompletion

noncomputable section

/-! A surjective completed divided-power presentation of the actual A_cris. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaDividedPowers OAI.NumberTheory.PadicHodge.WeakAdmissibility.BoundedCompletion

theorem modp_surjective_of_remainders {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (q : R) (f : M →ₗ[R] N) (h : ∀ y : N, ∃ x : M, ∃ z : N, y = f x + q • z) :
    Function.Surjective (Submodule.mkQ (Ideal.span {q} • (⊤ : Submodule R N)) ∘ₗ f) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨x, z, rfl⟩ := h y
  refine ⟨x, (Submodule.Quotient.eq _).mpr ?_⟩
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨-z, Submodule.mem_top, by simp only [smul_neg, sub_add_cancel_left]⟩

variable (p : ℕ) [Fact p.Prime]

instance aCrisAInfComplete : IsAdicComplete (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (Logarithm.PeriodRings.ACris p) := by
  apply (IsAdicComplete.map_algebraMap_iff (S := Logarithm.PeriodRings.ACrisUncompleted p)
    (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (Logarithm.PeriodRings.ACris p)).mp
  rw [Ideal.map_span, Set.image_singleton, map_natCast]
  exact AdicCompletion.isAdicComplete (Submodule.fg_span_singleton _)

def dividedPowerCombination : (ℕ →₀ Logarithm.PeriodRings.AInf p) →ₗ[Logarithm.PeriodRings.AInf p] Logarithm.PeriodRings.ACrisUncompleted p :=
  Finsupp.linearCombination (Logarithm.PeriodRings.AInf p) (ThetaDividedPowers.thetaDividedPower p)

theorem dividedPowerCombination_surjective : Function.Surjective (dividedPowerCombination p) := by
  apply (span_range_eq_top_iff_surjective_finsuppLinearCombination (Logarithm.PeriodRings.AInf p) (v := ThetaDividedPowers.thetaDividedPower p)).mp
  exact top_unique (fun x _ => ThetaDividedPowers.uncompleted_mem_span p x)

def dividedPowerToCompletion : (ℕ →₀ Logarithm.PeriodRings.AInf p) →ₗ[Logarithm.PeriodRings.AInf p] Logarithm.PeriodRings.ACris p :=
  (IsScalarTower.toAlgHom (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p)).toLinearMap.comp
    (dividedPowerCombination p)

def completedDividedPowers :
    AdicCompletion (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (ℕ →₀ Logarithm.PeriodRings.AInf p) →ₗ[Logarithm.PeriodRings.AInf p] Logarithm.PeriodRings.ACris p :=
  (AdicCompletion.ofLinearEquiv (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (Logarithm.PeriodRings.ACris p)).symm.toLinearMap.comp
    ((AdicCompletion.map (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (dividedPowerToCompletion p)).restrictScalars (Logarithm.PeriodRings.AInf p))

theorem completedDividedPowers_of (c : ℕ →₀ Logarithm.PeriodRings.AInf p) :
    completedDividedPowers p (AdicCompletion.of (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (ℕ →₀ Logarithm.PeriodRings.AInf p) c) =
      algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p) (dividedPowerCombination p c) := by
  change (AdicCompletion.ofLinearEquiv (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (Logarithm.PeriodRings.ACris p)).symm
    (AdicCompletion.map (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (dividedPowerToCompletion p)
      (AdicCompletion.of (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (ℕ →₀ Logarithm.PeriodRings.AInf p) c)) = _
  rw [AdicCompletion.map_of, AdicCompletion.ofLinearEquiv_symm_of]
  rfl

theorem completedDividedPowers_remainder (y : Logarithm.PeriodRings.ACris p) :
    ∃ c : ℕ →₀ Logarithm.PeriodRings.AInf p, ∃ z : Logarithm.PeriodRings.ACris p,
      y = completedDividedPowers p (AdicCompletion.of (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (ℕ →₀ Logarithm.PeriodRings.AInf p) c) +
        (p : Logarithm.PeriodRings.AInf p) • z := by
  obtain ⟨a, z, hy⟩ := BoundedCompletion.exists_remainder p y 1
  obtain ⟨c, hc⟩ := dividedPowerCombination_surjective p a
  refine ⟨c, z, ?_⟩
  have he := (completedDividedPowers_of p c).trans (congrArg (algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p)) hc)
  have hs : (p : Logarithm.PeriodRings.AInf p) • z = (p : Logarithm.PeriodRings.ACris p) * z := by rw [Algebra.smul_def, map_natCast]
  exact hy.trans ((congrArg₂ (· + ·) he.symm (by simpa only [pow_one] using hs.symm)))

theorem completedDividedPowers_modp :
    Function.Surjective (Submodule.mkQ ((Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) •
      (⊤ : Submodule (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACris p))) ∘ₗ completedDividedPowers p) := by
  apply modp_surjective_of_remainders
  intro y
  obtain ⟨c, z, hz⟩ := completedDividedPowers_remainder p y
  exact ⟨AdicCompletion.of (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (ℕ →₀ Logarithm.PeriodRings.AInf p) c, z, hz⟩

theorem completedDividedPowers_surjective : Function.Surjective (completedDividedPowers p) := by
  let : IsAdicComplete (Ideal.span {(p : Logarithm.PeriodRings.AInf p)})
      (AdicCompletion (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (ℕ →₀ Logarithm.PeriodRings.AInf p)) :=
    AdicCompletion.isAdicComplete (Submodule.fg_span_singleton _)
  exact surjective_of_mkQ_comp_surjective (I := Ideal.span {(p : Logarithm.PeriodRings.AInf p)})
    (completedDividedPowers_modp p)

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.DividedPowerCompletion
