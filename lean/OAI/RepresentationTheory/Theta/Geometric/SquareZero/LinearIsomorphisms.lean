import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Algebra.Module.Projective

/-! # Linear Isomorphisms -/

namespace OAI.RepresentationTheory.Theta.Geometric.SquareZero.LinearIsomorphisms

/-! Linear maps that are inverse modulo a square-zero ideal are
actual isomorphisms. This supplies the affine frame-lifting step for
infinitesimal line-bundle families. -/

variable {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]

theorem squareZero_smul_eq_zero (I : Ideal R) (hI : I * I = ⊥)
    {a : R} (ha : a ∈ I) {m : M} (hm : m ∈ I • (⊤ : Submodule R M)) : a • m = 0 := by
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro b hb x _
    rw [smul_smul]
    have hab : a * b = 0 := (Submodule.mem_bot R).mp (hI ▸ Ideal.mul_mem_mul ha hb)
    rw [hab, zero_smul]
  · intro x y hx hy
    rw [smul_add, hx, hy, add_zero]

theorem squareZero_linear_composite (I : Ideal R) (hI : I * I = ⊥)
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : ∀ m, f m ∈ I • (⊤ : Submodule R N))
    (hg : ∀ n, g n ∈ I • (⊤ : Submodule R P)) : g.comp f = 0 := by
  ext m
  change g (f m) = 0
  refine Submodule.smul_induction_on (hf m) ?_ ?_
  · intro a ha n _
    rw [map_smul]
    exact squareZero_smul_eq_zero I hI ha (hg n)
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

theorem linear_bijective_of_squareZero_inverse (I : Ideal R) (hI : I * I = ⊥)
    (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (hM : ∀ m, g (f m) - m ∈ I • (⊤ : Submodule R M))
    (hN : ∀ n, f (g n) - n ∈ I • (⊤ : Submodule R N)) : Function.Bijective f := by
  let dM := g.comp f - LinearMap.id
  let dN := f.comp g - LinearMap.id
  have hMM : dM.comp dM = 0 := squareZero_linear_composite I hI dM dM hM hM
  have hNN : dN.comp dN = 0 := squareZero_linear_composite I hI dN dN hN hN
  constructor
  · intro x y hxy
    have hz : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hd : dM (x - y) = -(x - y) := by
      change g (f (x - y)) - (x - y) = _
      rw [hz, map_zero, zero_sub]
    have he := LinearMap.congr_fun hMM (x - y)
    change dM (dM (x - y)) = 0 at he
    rw [hd, map_neg, hd, neg_neg] at he
    exact sub_eq_zero.mp he
  · intro y
    refine ⟨g (y - dN y), ?_⟩
    have he := LinearMap.congr_fun hNN y
    change dN (dN y) = 0 at he
    have hfg (z : N) : f (g z) = dN z + z := by
      change f (g z) = (f (g z) - z) + z
      exact (sub_add_cancel _ _).symm
    rw [hfg, map_sub, he, sub_zero]
    exact (add_sub_assoc (dN y) y (dN y)).symm.trans (add_sub_cancel_left (dN y) y)

end OAI.RepresentationTheory.Theta.Geometric.SquareZero.LinearIsomorphisms
