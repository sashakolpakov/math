import Mathlib

/-! # Rational -/

namespace OAI.RepresentationTheory.Hecke.Rational.CentralConstraintIntrinsic

noncomputable section

/-! Algebraicity from the actual scalar extension of a rational action.
No rationality compatibility or algebraicity assertion is a data field. -/

open scoped TensorProduct

def scalarExtendedAction {H V : Type*} [Ring H] [Algebra ℚ H]
    [AddCommGroup V] [Module ℚ V]
    (ρ : H →ₐ[ℚ] Module.End ℚ V) :
    ℂ ⊗[ℚ] H →ₐ[ℂ] Module.End ℂ (ℂ ⊗[ℚ] V) :=
  AlgHom.liftEquiv ℚ ℂ H (Module.End ℂ (ℂ ⊗[ℚ] V))
    ((Module.End.baseChangeHom ℚ ℂ V).comp ρ)

theorem scalarExtendedAction_tmul {H V : Type*} [Ring H] [Algebra ℚ H]
    [AddCommGroup V] [Module ℚ V]
    (ρ : H →ₐ[ℚ] Module.End ℚ V) (c : ℂ) (h : H) :
    scalarExtendedAction ρ (c ⊗ₜ[ℚ] h) = c • (ρ h).baseChange ℂ := rfl

theorem scalarExtendedAction_power {H V : Type*} [Ring H] [Algebra ℚ H]
    [AddCommGroup V] [Module ℚ V]
    (ρ : H →ₐ[ℚ] Module.End ℚ V) (h : H) (n : ℕ)
    (hn : (ρ h) ^ n = 1) :
    (scalarExtendedAction ρ (1 ⊗ₜ[ℚ] h)) ^ n = 1 := by
  rw [scalarExtendedAction_tmul, one_smul, ← LinearMap.baseChange_pow, hn,
    LinearMap.baseChange_one]

theorem rational_baseChange_nat_smul
    {V : Type*} [AddCommGroup V] [Module ℚ V] (f : Module.End ℚ V) (n : ℕ) :
    ((n : ℚ) • f).baseChange ℂ = (n : ℂ) • f.baseChange ℂ := by
  simp only [Nat.cast_smul_eq_nsmul]
  exact map_nsmul (Module.End.baseChangeHom ℚ ℂ V) n f

theorem rational_generalized_eigenvalue_algebraic
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (f : Module.End ℚ V) (z : ℂ)
    (hz : Module.End.genEigenspace (f.baseChange ℂ) z ⊤ ≠ ⊥) : IsAlgebraic ℚ z := by
  have he : Module.End.HasEigenvalue (f.baseChange ℂ) z :=
    Module.End.HasUnifEigenvalue.lt zero_lt_one hz
  have hr := (Module.End.hasEigenvalue_iff_isRoot_charpoly (f.baseChange ℂ) z).mp he
  rw [LinearMap.charpoly_baseChange] at hr
  refine ⟨f.charpoly, f.charpoly_monic.ne_zero, ?_⟩
  simpa only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def] using hr

theorem occurring_rational_eigenvalues_algebraic
    {H V : Type*} [Ring H] [Algebra ℚ H]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (ρ : H →ₐ[ℚ] Module.End ℚ V) (χ : ℂ ⊗[ℚ] H →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (scalarExtendedAction ρ h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (h : H) : IsAlgebraic ℚ (χ (1 ⊗ₜ[ℚ] h)) := by
  apply rational_generalized_eigenvalue_algebraic (ρ h)
  have hi : (scalarExtendedAction ρ (1 ⊗ₜ[ℚ] h)).genEigenspace
      (χ (1 ⊗ₜ[ℚ] h)) ⊤ ≠ ⊥ := by
    intro hz
    apply hχ
    apply le_antisymm _ bot_le
    rw [← hz]
    exact iInf_le _ (1 ⊗ₜ[ℚ] h)
  simpa only [scalarExtendedAction_tmul, one_smul] using hi

theorem cubic_parameters_algebraic (q : ℕ) (hq : q ≠ 0)
    (t₁ t₂ t₃ : ℂ) (ht₁ : IsAlgebraic ℚ t₁)
    (ht₂ : IsAlgebraic ℚ t₂) (ht₃ : IsAlgebraic ℚ t₃)
    (α : Fin 3 → ℂ)
    (h₁ : t₁ = (q : ℂ) * (α 0 + α 1 + α 2))
    (h₂ : t₂ = (q : ℂ) * (α 0 * α 1 + α 0 * α 2 + α 1 * α 2))
    (h₃ : t₃ = α 0 * α 1 * α 2) : ∀ i, IsAlgebraic ℚ (α i) := by
  classical
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hqalg : IsAlgebraic ℚ (q : ℂ) := isAlgebraic_natCast q
  have hs : IsIntegral ℚ (t₁ / (q : ℂ)) := by
    simpa only [div_eq_mul_inv] using (ht₁.mul hqalg.inv).isIntegral
  have hp : IsIntegral ℚ (t₂ / (q : ℂ)) := by
    simpa only [div_eq_mul_inv] using (ht₂.mul hqalg.inv).isIntegral
  let p : Polynomial ℂ := Polynomial.X ^ 3 - Polynomial.C (t₁ / q) * Polynomial.X ^ 2 +
    Polynomial.C (t₂ / q) * Polynomial.X - Polynomial.C t₃
  have peq : p = (Polynomial.X - Polynomial.C (α 0)) *
      (Polynomial.X - Polynomial.C (α 1)) * (Polynomial.X - Polynomial.C (α 2)) := by
    dsimp [p]
    rw [h₁, h₂, h₃]
    simp only [mul_div_cancel_left₀ _ hqC, map_add, map_mul]
    ring
  have hm : p.Monic := by
    rw [peq]
    exact ((Polynomial.monic_X_sub_C _).mul (Polynomial.monic_X_sub_C _)).mul
      (Polynomial.monic_X_sub_C _)
  have hd : p.natDegree ≠ 0 := by
    intro hd
    have hz : p.coeff 3 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    norm_num [p] at hz
  have hc (n : ℕ) : IsIntegral ℚ (p.coeff n) := by
    dsimp [p]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    split_ifs <;> simp only [mul_one, mul_zero, sub_zero, add_zero,
      zero_add, zero_sub] <;>
      repeat first | apply IsIntegral.sub | apply IsIntegral.add | apply IsIntegral.neg |
        exact isIntegral_zero | exact isIntegral_one | exact hs | exact hp | exact ht₃.isIntegral
  intro i
  have hz : p.eval (α i) = 0 := by
    rw [peq]
    fin_cases i <;> simp
  exact (IsIntegral.of_aeval_monic_of_isIntegral_coeff hm hd
    (hz ▸ isIntegral_zero) hc).isAlgebraic

theorem projective_parameter_algebraic (r e : ℂ) (hr : r ≠ 0)
    (hralg : IsAlgebraic ℚ r) (α : Fin 3 → ℂ)
    (hαalg : ∀ i, IsAlgebraic ℚ (α i))
    (hproj : ∃ a : ℂ, a ≠ 0 ∧ ∃ σ : Equiv.Perm (Fin 3),
      ∀ i, α i = a * (![r, r⁻¹, e] : Fin 3 → ℂ) (σ i)) :
    IsAlgebraic ℚ e := by
  obtain ⟨a, ha, σ, hσ⟩ := hproj
  have h₀ := hσ (σ.symm 0)
  have h₂ := hσ (σ.symm 2)
  simp only [Equiv.apply_symm_apply] at h₀ h₂
  change α (σ.symm 0) = a * r at h₀
  change α (σ.symm 2) = a * e at h₂
  have halg : IsAlgebraic ℚ a := by
    have h := (hαalg (σ.symm 0)).mul hralg.inv
    simpa only [h₀, mul_assoc, mul_inv_cancel₀ hr, mul_one] using h
  have h := (hαalg (σ.symm 2)).mul halg.inv
  have heq : α (σ.symm 2) * a⁻¹ = e := by
    rw [h₂]
    field_simp
  simpa only [heq] using h

end

end OAI.RepresentationTheory.Hecke.Rational.CentralConstraintIntrinsic
