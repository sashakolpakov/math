import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinates
import Mathlib.LinearAlgebra.Pi

/-! # Integral Block Lattice -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralBlockLattice.TestTransport

noncomputable section

/-! A product of local special-linear blocks preserves the integral
product lattice exactly when every block is in the literal integral group. -/

open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime] {S : Type*} [DecidableEq S]

def localBlockLinear (A : S → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    (S → Fin 3 → Padic q) →ₗ[Padic q] (S → Fin 3 → Padic q) :=
  LinearMap.pi (fun v => (A v).val.mulVecLin.comp (LinearMap.proj v))

omit [DecidableEq S] in
theorem localBlockLinear_apply (A : S → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) (x : S → Fin 3 → Padic q) (v : S) :
    localBlockLinear q A x v = (A v).val *ᵥ x v := rfl

theorem localBlock_preserves_iff (M : Submodule (PadicInt q) (S → Fin 3 → Padic q))
    (hM : ∀ x, x ∈ M ↔ ∀ v i, ‖x v i‖ ≤ 1) (A : S → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    (∀ x ∈ M, localBlockLinear q A x ∈ M) ↔ ∀ v, A v ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q := by
  constructor
  · intro h v
    apply (IntegralCoordinates.TestTransport.integralSL3_iff_preserves_vectors q (A v)).mpr
    intro x hx i
    have hy : Pi.single v x ∈ M := by
      apply (hM _).mpr
      intro w j
      by_cases hw : w = v
      · subst w
        simpa using hx j
      · simp [Pi.single_eq_of_ne hw]
    have hb := (hM _).mp (h _ hy) v i
    simpa only [localBlockLinear_apply, Pi.single_eq_same] using hb
  · intro h x hx
    apply (hM _).mpr
    intro v i
    exact IntegralCoordinates.TestTransport.integralSL3_mulVec_integral q (A v) (h v) (x v) ((hM x).mp hx v) i

omit [DecidableEq S] in
theorem identity_blocks_integral_iff {G : Type*} [Group G] (U : Subgroup G)
    (p : S → Prop) [DecidablePred p] (A : S → G) :
    (∀ v, (if p v then 1 else A v) ∈ U) ↔ ∀ v, ¬ p v → A v ∈ U := by
  constructor
  · intro h v hv
    simpa only [ite_eq_right hv] using h v
  · intro h v
    by_cases hv : p v
    · simpa only [ite_eq_left hv] using U.one_mem
    · simpa only [ite_eq_right hv] using h v hv

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralBlockLattice.TestTransport
