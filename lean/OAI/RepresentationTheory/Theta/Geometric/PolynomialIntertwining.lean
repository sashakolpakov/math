import Mathlib.LinearAlgebra.Charpoly.Basic

/-! # Polynomial Intertwining -/

namespace OAI.RepresentationTheory.Theta.Geometric.PolynomialIntertwining

noncomputable section

/-! Polynomial evaluation respects an actual intertwining linear map,
including when the target has a larger scalar ring. -/

open _root_.Polynomial

variable {R S V W : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] [Module S W] [IsScalarTower R S W]

theorem polynomial_intertwining_apply (f : Module.End R V) (g : Module.End S W)
    (i : V →ₗ[R] W) (hi : ∀ x, g (i x) = i (f x)) (p : R[X]) (x : V) :
    aeval g p (i x) = i (aeval f p x) := by
  have hpow (n : ℕ) : ∀ x, (g ^ n) (i x) = i ((f ^ n) x) := by
    induction n with
    | zero => intro x; rfl
    | succ n hn =>
      intro x
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hn, hi]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq, map_add]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply,
      hpow, map_smul]

end

end OAI.RepresentationTheory.Theta.Geometric.PolynomialIntertwining
