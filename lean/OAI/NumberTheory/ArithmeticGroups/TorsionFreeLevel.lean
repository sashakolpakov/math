import OAI.NumberTheory.ArithmeticGroups.Levels

/-! # Torsion Free Level -/

namespace OAI.NumberTheory.ArithmeticGroups.TorsionFreeLevel

/-!
# TorsionFreeLevel: Torsion-free sufficiently deep principal levels

This proves the declarations in `Statements/TorsionFreeLevel.lean` without importing that
statement module. The integral congruence theorem is supplied by the proved
`Levels` module. As in the specification, the arithmetic matrix group uses
the three-dimensional CM-field unitary model, and the ball action is abstracted
as a group action with explicitly assumed finite point stabilizers.
-/

open OAI.NumberTheory.ArithmeticGroups.Levels.CongruenceLevel

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E]

/-- Every prescribed positive level admits a torsion-free refinement,
and all positive multiples of that refinement are torsion-free. -/
theorem sufficiently_deep_principal_levels_torsion_free
    (b : E) (Λ : Submodule ℤ (Data.CongruenceLevel.VE E))
    (hΛ : Data.CongruenceLevel.FullStableLattice Λ)
    (N₀ : ℕ) (hN₀ : 0 < N₀) :
    ∃ N : ℕ, 3 ≤ N ∧ N₀ ∣ N ∧
      ∀ M : ℕ, 0 < M → N ∣ M →
        ∀ g : Data.CongruenceLevel.VE E ≃ₗ[E] Data.CongruenceLevel.VE E,
          Data.CongruenceLevel.PrincipalLevel b Λ M g →
          ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1 := by
  have hN : 3 ≤ 3 * N₀ := by omega
  refine ⟨3 * N₀, hN, dvd_mul_left N₀ 3, ?_⟩
  intro M hM hNM g hg k hk hpow
  exact Levels.CongruenceLevel.principalLevel_torsion_free b Λ hΛ M
    (hN.trans (Nat.le_of_dvd hM hNM)) g hg k hk hpow

/-- For an action with finite point stabilizers, elements of a
principal level at least three fixing a point are identities. -/
theorem principal_level_has_no_nontrivial_stabilizers
    (b : E) (Λ : Submodule ℤ (Data.CongruenceLevel.VE E))
    (hΛ : Data.CongruenceLevel.FullStableLattice Λ)
    (N : ℕ) (hN : 3 ≤ N)
    (Γ : Subgroup (Data.CongruenceLevel.VE E ≃ₗ[E] Data.CongruenceLevel.VE E))
    (X : Type*) [MulAction Γ X]
    (hfinite : ∀ x : X,
      (MulAction.stabilizer Γ x : Set Γ).Finite) :
    ∀ (g : Γ) (x : X),
      Data.CongruenceLevel.PrincipalLevel b Λ N (g : Data.CongruenceLevel.VE E ≃ₗ[E] Data.CongruenceLevel.VE E) →
      g • x = x → g = 1 := by
  intro g x hg hfix
  let : Finite (MulAction.stabilizer Γ x) := (hfinite x).to_subtype
  let s : MulAction.stabilizer Γ x :=
    ⟨g, MulAction.mem_stabilizer_iff.mpr hfix⟩
  have hpow : (g : Data.CongruenceLevel.VE E ≃ₗ[E] Data.CongruenceLevel.VE E) ^ orderOf s = 1 := by
    exact congrArg
      (fun y : MulAction.stabilizer Γ x => ((y : Γ) : Data.CongruenceLevel.VE E ≃ₗ[E] Data.CongruenceLevel.VE E))
      (pow_orderOf_eq_one s)
  apply Subtype.ext
  exact Levels.CongruenceLevel.principalLevel_torsion_free b Λ hΛ N hN
    (g : Data.CongruenceLevel.VE E ≃ₗ[E] Data.CongruenceLevel.VE E) hg (orderOf s) (orderOf_pos s) hpow

end OAI.NumberTheory.ArithmeticGroups.TorsionFreeLevel
