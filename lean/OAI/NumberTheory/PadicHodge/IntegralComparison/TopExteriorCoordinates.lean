import OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorDeterminant

/-! # Top Exterior Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorCoordinates

noncomputable section

/-! A finite basis gives exact coordinates on the top exterior power.
These coordinates use its determinant form and its actual wedge generator. -/

universe u v

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
  {n : ℕ} (b : Module.Basis (Fin n) R V)

def coordinate : (⋀[R]^n V) →ₗ[R] R := exteriorPower.alternatingMapLinearEquiv b.det

def generator : ⋀[R]^n V := exteriorPower.ιMulti R n b

theorem coordinate_wedge (v : Fin n → V) :
    coordinate b (exteriorPower.ιMulti R n v) = b.det v :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

theorem coordinate_generator : coordinate b (generator b) = 1 := by
  rw [generator, coordinate_wedge, Module.Basis.det_self]

theorem reconstruct (x : ⋀[R]^n V) : coordinate b x • generator b = x := by
  have h : (LinearMap.toSpanSingleton R (⋀[R]^n V) (generator b)).comp (coordinate b) =
      LinearMap.id := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span R n V)
    rintro x ⟨v, rfl⟩
    change coordinate b (exteriorPower.ιMulti R n v) • generator b = exteriorPower.ιMulti R n v
    rw [coordinate_wedge]
    exact (TopExteriorDeterminant.alternating_apply_eq_det_smul b
      (exteriorPower.ιMulti R n) v).symm
  exact LinearMap.congr_fun h x

def equiv : (⋀[R]^n V) ≃ₗ[R] R where
  __ := coordinate b
  invFun r := r • generator b
  left_inv := reconstruct b
  right_inv r := by
    change coordinate b (r • generator b) = r
    rw [map_smul, coordinate_generator, smul_eq_mul, mul_one]

@[simp] theorem equiv_apply (x : ⋀[R]^n V) : equiv b x = coordinate b x := rfl

@[simp] theorem equiv_symm_apply (r : R) : (equiv b).symm r = r • generator b := rfl

theorem coordinate_eq {b' : Module.Basis (Fin n) R V} (h : b.det = b'.det) :
    coordinate b = coordinate b' := congrArg exteriorPower.alternatingMapLinearEquiv h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorCoordinates
