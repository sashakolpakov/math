import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.InfinitesimalEq
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Affine Lifting Eq -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.AffineLiftingEq.AffineLifting

/-!
# TorsionQuotient: uniqueness of lifts for multiplication on affine group points

The target algebra is arbitrary. The inverse is constructed using the
antipode; no bialgebra structure on the test algebra is assumed.
-/

open _root_.Algebra Coalgebra Bialgebra HopfAlgebra TensorProduct WithConv

variable {R B C D : Type*} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
variable [HopfAlgebra R B] [Algebra R C] [Algebra R D]

/-- Inversion of a point represented by an algebra homomorphism. -/
noncomputable def inverseCharacter (f : WithConv (B →ₐ[R] C)) : WithConv (B →ₐ[R] C) :=
  toConv (f.ofConv.comp (HopfAlgebra.antipodeAlgHom R B))

theorem inverseCharacter_mul (f : WithConv (B →ₐ[R] C)) :
    inverseCharacter f * f = 1 := by
  have H : (lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv) =
      f.ofConv.comp (lmul' R) := by ext <;> simp
  trans toConv (((lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv)).comp
    ((Algebra.TensorProduct.map
      (HopfAlgebra.antipodeAlgHom R B) (.id _ _)).comp (comulAlgHom R B)))
  · rw [AlgHom.comp_assoc,
      ← AlgHom.comp_assoc (Algebra.TensorProduct.map f.ofConv f.ofConv),
      ← Algebra.TensorProduct.map_comp]
    rfl
  rw [H, AlgHom.comp_assoc, WithConv.ext_iff, ← AlgHom.toLinearMap_injective.eq_iff]
  change f.ofConv.toLinearMap.comp
    (toConv (antipode R (A := B)) * toConv LinearMap.id).ofConv =
      ofConv (1 : WithConv (B →ₗ[R] C))
  rw [LinearMap.antipode_mul_id]
  ext
  simp

/-- Change of test algebra preserves convolution and its identity. -/
def mapCharacter (p : C →ₐ[R] D) :
    WithConv (B →ₐ[R] C) →* WithConv (B →ₐ[R] D) where
  toFun f := toConv (p.comp f.ofConv)
  map_one' := by
    ext b
    exact p.commutes (counit (R := R) b)
  map_mul' f g := by
    apply WithConv.ext
    exact AlgHom.comp_convMul_distrib p f g

variable [IsCocomm R B]

/-- Two points which coincide modulo a square-zero ideal, and have equal
multiples by an invertible m, coincide before reduction. -/
theorem character_eq_of_same_power_and_reduction
    (J : Ideal C) (hJ : J ^ 2 = ⊥)
    (f g : WithConv (B →ₐ[R] C))
    (hfg : ∀ b, f b - g b ∈ J)
    (m : ℕ) (hm : IsUnit (m : C)) (hpower : f ^ m = g ^ m) : f = g := by
  let q := mapCharacter (B := B) (Ideal.Quotient.mkₐ R J)
  have hq : q f = q g := by
    ext b
    exact Ideal.Quotient.eq.mpr (hfg b)
  have hinv : g * inverseCharacter g = 1 := by
    rw [mul_comm]
    exact inverseCharacter_mul g
  have hqone : q (f * inverseCharacter g) = 1 := by
    rw [map_mul, hq, ← map_mul, hinv, map_one]
  have hdeviation : ∀ b,
      (f * inverseCharacter g) b - algebraMap R C (counit (R := R) b) ∈ J := by
    intro b
    apply Ideal.Quotient.eq.mp
    have hb := congrArg (fun z : WithConv (B →ₐ[R] (C ⧸ J)) => z b) hqone
    exact hb
  have hp : (f * inverseCharacter g) ^ m = 1 := by
    rw [mul_pow, hpower, ← mul_pow, hinv, one_pow]
  have he := InfinitesimalEq.Infinitesimal.character_eq_one_of_power_eq_one J hJ
    (f * inverseCharacter g) hdeviation m hm hp
  have hcancel := congrArg (fun z => z * g) he
  simpa only [mul_assoc, inverseCharacter_mul, mul_one, one_mul] using hcancel

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.AffineLiftingEq.AffineLifting
