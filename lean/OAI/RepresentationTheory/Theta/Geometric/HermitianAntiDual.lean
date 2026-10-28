import OAI.RepresentationTheory.Theta.Geometric.Period.Hermitian
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Hermitian Anti Dual -/

namespace OAI.RepresentationTheory.Theta.Geometric.HermitianAntiDual

noncomputable section

/-! A positive Hermitian form realizes every antiholomorphic linear
functional by pairing with an actual translation vector. -/

set_option backward.isDefEq.respectTransparency false

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
    [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]
    (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)

def hermitianRealDualMap : V →ₗ[ℝ] Module.Dual ℂ V where
  toFun := H
  map_add' := H.map_add
  map_smul' r a := by
    ext z
    change H (r • a) z = r • H a z
    rw [← IsScalarTower.algebraMap_smul ℂ r a]
    have h := congrArg (fun f : Module.Dual ℂ V => f z) (H.map_smulₛₗ (r : ℂ) a)
    change H ((r : ℂ) • a) z = star (r : ℂ) * H a z at h
    rw [Complex.star_def, Complex.conj_ofReal] at h
    exact h

theorem hermitianRealDualMap_bijective
    (hpos : ∀ a, a ≠ 0 → 0 < (H a a).re) : Function.Bijective (hermitianRealDualMap H) := by
  let : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ ℂ V
  let : FiniteDimensional ℝ (Module.Dual ℂ V) := FiniteDimensional.trans ℝ ℂ (Module.Dual ℂ V)
  have hinj : Function.Injective (hermitianRealDualMap H) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro a ha
    by_contra hn
    have h := congrArg (fun f : Module.Dual ℂ V => (f a).re) ha
    exact (ne_of_gt (hpos a hn)) h
  have hdim : Module.finrank ℝ V = Module.finrank ℝ (Module.Dual ℂ V) := by
    rw [← Module.finrank_mul_finrank ℝ ℂ V,
      ← Module.finrank_mul_finrank ℝ ℂ (Module.Dual ℂ V), Subspace.dual_finrank_eq]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

theorem exists_hermitian_antilinear_representative
    (hsym : ∀ a b, H b a = star (H a b))
    (hpos : ∀ a, a ≠ 0 → 0 < (H a a).re) (f : V →ₗ⋆[ℂ] ℂ) :
    ∃ a : V, ∀ z, H z a = f z := by
  let g : Module.Dual ℂ V :=
    { toFun := fun z => star (f z)
      map_add' := by intro a b; rw [map_add, star_add]
      map_smul' := by
        intro c a
        rw [map_smulₛₗ]
        simp only [starRingEnd_apply, smul_eq_mul, star_mul, star_star, RingHom.id_apply]
        exact mul_comm _ _ }
  obtain ⟨a, ha⟩ := (hermitianRealDualMap_bijective H hpos).2 g
  refine ⟨a, fun z => ?_⟩
  have hz := congrArg (fun l : Module.Dual ℂ V => l z) ha
  change H a z = star (f z) at hz
  rw [hsym a z, hz, star_star]

theorem hermitianAntiDual_bijective
    (hsym : ∀ a b, H b a = star (H a b))
    (hpos : ∀ a, a ≠ 0 → 0 < (H a a).re) : Function.Bijective H.flip := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro a ha
    by_contra hn
    have h := congrArg (fun f : V →ₗ⋆[ℂ] ℂ => (f a).re) ha
    exact (ne_of_gt (hpos a hn)) h
  · intro f
    obtain ⟨a, ha⟩ := exists_hermitian_antilinear_representative H hsym hpos f
    exact ⟨a, LinearMap.ext ha⟩

def hermitianAntiDualEquiv
    (hsym : ∀ a b, H b a = star (H a b))
    (hpos : ∀ a, a ≠ 0 → 0 < (H a a).re) : V ≃ₗ[ℂ] (V →ₗ⋆[ℂ] ℂ) :=
  LinearEquiv.ofBijective H.flip (hermitianAntiDual_bijective H hsym hpos)

theorem hermitianAntiDualEquiv_apply
    (hsym : ∀ a b, H b a = star (H a b))
    (hpos : ∀ a, a ≠ 0 → 0 < (H a a).re) (a z : V) :
    hermitianAntiDualEquiv H hsym hpos a z = H z a := rfl

end

end OAI.RepresentationTheory.Theta.Geometric.HermitianAntiDual
