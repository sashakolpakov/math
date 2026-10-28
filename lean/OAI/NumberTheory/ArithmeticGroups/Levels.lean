import OAI.NumberTheory.ArithmeticGroups.Congruence
import OAI.NumberTheory.ArithmeticGroups.Data

/-! # Levels -/

namespace OAI.NumberTheory.ArithmeticGroups.Levels.CongruenceLevel

noncomputable section

open scoped Classical

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E]

theorem principalLevel_torsion_free
    (b : E) (Λ : Submodule ℤ (Data.CongruenceLevel.VE E)) (hΛ : Data.CongruenceLevel.FullStableLattice Λ)
    (N : ℕ) (hN : 3 ≤ N) (g : Data.CongruenceLevel.VE E ≃ₗ[E] Data.CongruenceLevel.VE E)
    (hg : Data.CongruenceLevel.PrincipalLevel b Λ N g)
    (k : ℕ) (hk : 0 < k) (hpow : g ^ k = 1) : g = 1 := by
  let : Module.Finite ℤ Λ := Module.Finite.of_fg hΛ.1
  let f : Module.End ℤ Λ := (g.toLinearMap.restrictScalars ℤ).restrict
    (fun x hx => (hg.2.1 x).mp hx)
  have hp (n : ℕ) (x : Λ) : ((f ^ n) x : Data.CongruenceLevel.VE E) = (g ^ n) (x : Data.CongruenceLevel.VE E) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply, LinearEquiv.mul_apply]
      change g (((f ^ n) x : Λ) : Data.CongruenceLevel.VE E) = g ((g ^ n) (x : Data.CongruenceLevel.VE E))
      rw [ih]
  have hf : f = 1 := by
    apply Congruence.Level.finite_lattice_congruence_torsion f N hN
      (k := k) (hk := hk)
    · intro x
      obtain ⟨y, hy, hxy⟩ := hg.2.2 x x.property
      refine ⟨⟨y, hy⟩, ?_⟩
      apply Subtype.ext
      change g (x : Data.CongruenceLevel.VE E) - (x : Data.CongruenceLevel.VE E) = N • y
      simpa only [natCast_zsmul] using hxy
    · apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [hp, hpow]
      rfl
  let D : Data.CongruenceLevel.VE E →ₗ[ℚ] Data.CongruenceLevel.VE E := g.toLinearMap.restrictScalars ℚ - LinearMap.id
  have hspan : Submodule.span ℚ (Λ : Set (Data.CongruenceLevel.VE E)) ≤ D.ker := by
    apply Submodule.span_le.mpr
    intro x hx
    have h := LinearMap.congr_fun hf (⟨x, hx⟩ : Λ)
    have h' := congrArg (fun y : Λ => (y : Data.CongruenceLevel.VE E)) h
    change g x = x at h'
    change g x - x = 0
    exact sub_eq_zero.mpr h'
  rw [hΛ.2.1] at hspan
  apply LinearEquiv.ext
  intro x
  have h := hspan (Submodule.mem_top : x ∈ (⊤ : Submodule ℚ (Data.CongruenceLevel.VE E)))
  change g x - x = 0 at h
  exact sub_eq_zero.mp h

theorem arbitrarily_deep_principal_levels
    (b : E) (Λ : Submodule ℤ (Data.CongruenceLevel.VE E)) (hΛ : Data.CongruenceLevel.FullStableLattice Λ)
    (N₀ : ℕ) (hN₀ : 0 < N₀) :
    ∃ N : ℕ, 3 ≤ N ∧ N₀ ∣ N ∧
      ∀ g : Data.CongruenceLevel.VE E ≃ₗ[E] Data.CongruenceLevel.VE E, Data.CongruenceLevel.PrincipalLevel b Λ N g →
        ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1 := by
  refine ⟨3 * N₀, by omega, dvd_mul_left N₀ 3, ?_⟩
  intro g hg k hk hp
  exact principalLevel_torsion_free b Λ hΛ _ (by omega) g hg k hk hp

end

end OAI.NumberTheory.ArithmeticGroups.Levels.CongruenceLevel
