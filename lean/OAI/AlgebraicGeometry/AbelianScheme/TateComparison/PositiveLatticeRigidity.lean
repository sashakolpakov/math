import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PositiveLatticeTorsion
import OAI.NumberTheory.ArithmeticGroups.Congruence

/-! # Positive Lattice Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PositiveLatticeRigidity

noncomputable section

/-! A positive lattice isometry preserving full level at least three is
the identity. Finite order is proved from positivity and lattice discreteness. -/

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I]

theorem positiveLattice_congruence_eq_one (b : Module.Basis I ℝ V)
    (Q : V → ℝ) (hc : Continuous Q)
    (hs : ∀ (a : ℝ) (x : V), Q (a • x) = a ^ 2 * Q x)
    (hp : ∀ x : V, x ≠ 0 → 0 < Q x) (f : V ≃ₗ[ℝ] V)
    (hf : ∀ x : V, Q (f x) = Q x)
    (hL : ∀ x ∈ Submodule.span ℤ (Set.range b), f x ∈ Submodule.span ℤ (Set.range b))
    (N : ℕ) (hN : 3 ≤ N)
    (hcong : ∀ x ∈ Submodule.span ℤ (Set.range b),
      ∃ y ∈ Submodule.span ℤ (Set.range b), f x - x = N • y) : f = 1 := by
  obtain ⟨k, hk, hpow⟩ := (PositiveLatticeTorsion.positiveLattice_isOfFinOrder b Q hc hs hp f hf hL).exists_pow_eq_one
  let L := Submodule.span ℤ (Set.range b)
  have : Module.Finite ℤ L := Module.Finite.of_fg (Submodule.fg_span (Set.finite_range b))
  let a : Module.End ℤ L := (f.toLinearMap.restrictScalars ℤ).restrict hL
  have ha (n : ℕ) (x : L) : ((a ^ n) x).val = (f ^ n) x.val := by
    induction n with
    | zero => rfl
    | succ n hn =>
      simp only [pow_succ', Module.End.mul_apply, LinearEquiv.mul_apply]
      exact congrArg f hn
  have hid : a = 1 := by
    apply NumberTheory.ArithmeticGroups.Congruence.Level.finite_lattice_congruence_torsion a N hN
      (k := k) (hk := hk)
    · intro x
      obtain ⟨y, hy, he⟩ := hcong x.val x.property
      exact ⟨⟨y, hy⟩, Subtype.ext he⟩
    · apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [ha, hpow]
      rfl
  apply LinearEquiv.toLinearMap_injective
  apply b.ext
  intro i
  exact congrArg Subtype.val
    (LinearMap.congr_fun hid (⟨b i, Submodule.subset_span ⟨i, rfl⟩⟩ : L))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PositiveLatticeRigidity
