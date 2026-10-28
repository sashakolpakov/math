import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Groups
import OAI.NumberTheory.ArithmeticGroups.Congruence

/-! # Lattice Torsion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.LatticeTorsion

noncomputable section

/-! Congruence to the identity at level at least three excludes torsion
on any finitely generated lattice spanning a characteristic-zero vector
space. No preserved form is needed. -/

theorem principalLattice_torsion_free
    {R V : Type*} [Field R] [CharZero R] [AddCommGroup V] [Module R V]
    (Λ : Submodule ℤ V) (hfg : Λ.FG) (hspan : Submodule.span R (Λ : Set V) = ⊤)
    (N : ℕ) (hN : 3 ≤ N) (g : V ≃ₗ[R] V)
    (hg : g ∈ Groups.principalLatticeSubgroup (R := R) Λ.toAddSubgroup N)
    (k : ℕ) (hk : 0 < k) (hpow : g ^ k = 1) : g = 1 := by
  let : Module.IsTorsionFree ℤ V := Module.IsTorsionFree.trans R
  let : Module.Finite ℤ Λ := Module.Finite.of_fg hfg
  let f : Module.End ℤ Λ := (g.toLinearMap.restrictScalars ℤ).restrict
    (fun x hx => (hg.1 x).mp hx)
  have hp (n : ℕ) (x : Λ) : ((f ^ n) x : V) = (g ^ n) (x : V) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply, LinearEquiv.mul_apply]
      exact congrArg g ih
  have hf : f = 1 := by
    apply NumberTheory.ArithmeticGroups.Congruence.Level.finite_lattice_congruence_torsion f N hN (k := k) (hk := hk)
    · intro x
      obtain ⟨y, hy, hxy⟩ := hg.2 x x.property
      exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
    · apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [hp, hpow]
      rfl
  let D : V →ₗ[R] V := g.toLinearMap - LinearMap.id
  have hker : Submodule.span R (Λ : Set V) ≤ D.ker := by
    apply Submodule.span_le.mpr
    intro x hx
    have h := congrArg (fun y : Λ => (y : V)) (LinearMap.congr_fun hf ⟨x, hx⟩)
    change g x = x at h
    exact sub_eq_zero.mpr h
  rw [hspan] at hker
  apply LinearEquiv.ext
  intro x
  exact sub_eq_zero.mp (hker (Submodule.mem_top : x ∈ (⊤ : Submodule R V)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.LatticeTorsion
