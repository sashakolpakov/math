import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PositiveQuadraticBounds
import Mathlib.Algebra.Module.ZLattice.Basic

/-! # Positive Lattice Torsion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PositiveLatticeTorsion

noncomputable section

/-! A lattice automorphism preserving a positive quadratic function
has finite order: each basis vector has a finite bounded lattice orbit. -/

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I]

theorem positiveLattice_isOfFinOrder (b : Module.Basis I ℝ V)
    (Q : V → ℝ) (hc : Continuous Q)
    (hs : ∀ (a : ℝ) (x : V), Q (a • x) = a ^ 2 * Q x)
    (hp : ∀ x : V, x ≠ 0 → 0 < Q x) (f : V ≃ₗ[ℝ] V)
    (hf : ∀ x : V, Q (f x) = Q x)
    (hL : ∀ x ∈ Submodule.span ℤ (Set.range b), f x ∈ Submodule.span ℤ (Set.range b)) :
    IsOfFinOrder f := by
  let L := Submodule.span ℤ (Set.range b)
  have hpow (n : ℕ) : (∀ x : V, Q ((f ^ n) x) = Q x) ∧
      ∀ x ∈ L, (f ^ n) x ∈ L := by
    induction n with
    | zero => exact ⟨fun _ => rfl, fun _ hx => hx⟩
    | succ n hn =>
      constructor
      · intro x
        simp only [pow_succ', LinearEquiv.mul_apply, hf, hn.1]
      · intro x hx
        rw [pow_succ', LinearEquiv.mul_apply]
        exact hL _ (hn.2 x hx)
  let S (i : I) : Set V := {x : V | Q x ≤ Q (b i)} ∩ L
  have hS (i : I) : (S i).Finite :=
    ZSpan.setFinite_inter b (PositiveQuadraticBounds.positiveQuadratic_sublevel_bounded Q hc hs hp (Q (b i)))
  have (i : I) : Finite (S i) := (hS i).to_subtype
  let j : Submonoid.powers f → ∀ i : I, S i := fun g i => ⟨g.val (b i), by
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff g.val f).mp g.property
    rw [← hn]
    exact ⟨(hpow n).1 (b i) |>.le,
      (hpow n).2 (b i) (Submodule.subset_span ⟨i, rfl⟩)⟩⟩
  have hj : Function.Injective j := by
    intro g h hgh
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro i
    exact congrArg Subtype.val (congrFun hgh i)
  have : Finite (Submonoid.powers f) := Finite.of_injective j hj
  exact finite_powers.mp (Set.toFinite (Submonoid.powers f : Set (V ≃ₗ[ℝ] V)))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PositiveLatticeTorsion
