import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.Ring

/-! # Infinitesimal Eq -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.InfinitesimalEq.Infinitesimal

/-!
# TorsionQuotient: square-zero linearization of affine commutative group points

Convolution is the point-group law for a cocommutative bialgebra. Modulo a
square-zero ideal, the deviation from the identity has square-zero
convolution product. This gives the linearization of multiplication by m.
-/

open _root_.Algebra Coalgebra Bialgebra WithConv

theorem one_add_square_zero_pow {D : Type*} [CommRing D]
    (x : D) (hx : x ^ 2 = 0) (n : ℕ) :
    (1 + x) ^ n = 1 + (n : D) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_add, Nat.cast_one]
    calc
      (1 + (n : D) * x) * (1 + x) = 1 + ((n : D) + 1) * x + (n : D) * x ^ 2 := by ring
      _ = 1 + ((n : D) + 1) * x := by rw [hx, mul_zero, add_zero]

variable {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
variable [Bialgebra R B] [IsCocomm R B] [Algebra R C]

theorem mul_eq_zero_of_square_zero_ideal (J : Ideal C) (hJ : J ^ 2 = ⊥)
    {a b : C} (ha : a ∈ J) (hb : b ∈ J) : a * b = 0 := by
  have h := Ideal.mul_mem_mul ha hb
  rw [← pow_two, hJ] at h
  exact Ideal.mem_bot.mp h

omit [IsCocomm R B] in
theorem conv_square_zero (J : Ideal C) (hJ : J ^ 2 = ⊥)
    (f : WithConv (B →ₗ[R] C)) (hf : ∀ b, f b ∈ J) : f ^ 2 = 0 := by
  rw [pow_two]
  ext b
  rw [(ℛ R b).convMul_apply]
  exact Finset.sum_eq_zero fun i _ => mul_eq_zero_of_square_zero_ideal J hJ
    (hf ((ℛ R b).left i)) (hf ((ℛ R b).right i))

/-- Linearization in the convolution algebra of linear maps. -/
theorem conv_power_linearization (J : Ideal C) (hJ : J ^ 2 = ⊥)
    (f : WithConv (B →ₗ[R] C))
    (hf : ∀ b, f b - algebraMap R C (counit (R := R) b) ∈ J) (m : ℕ) :
    f ^ m = 1 + (m : WithConv (B →ₗ[R] C)) * (f - 1) := by
  have hsquare : (f - 1) ^ 2 = 0 :=
    conv_square_zero J hJ (f - 1) hf
  simpa only [add_sub_cancel] using one_add_square_zero_pow (f - 1) hsquare m

/-- On each coordinate function, convolution powers multiply the first-order
deviation from the identity by m. -/
theorem character_power_apply (J : Ideal C) (hJ : J ^ 2 = ⊥)
    (f : WithConv (B →ₐ[R] C))
    (hf : ∀ b, f b - algebraMap R C (counit (R := R) b) ∈ J)
    (m : ℕ) (b : B) :
    (f ^ m) b = algebraMap R C (counit (R := R) b) +
      (m : C) * (f b - algebraMap R C (counit (R := R) b)) := by
  have h := congrArg (fun z : WithConv (B →ₗ[R] C) => z b)
    (conv_power_linearization J hJ (toConv f.ofConv.toLinearMap) hf m)
  rw [← AlgHom.toLinearMap_convPow] at h
  have hmul : (m : WithConv (B →ₗ[R] C)) * (toConv f.ofConv.toLinearMap - 1) =
      m • (toConv f.ofConv.toLinearMap - 1) := (nsmul_eq_mul m _).symm
  rw [hmul] at h
  change (f ^ m) b = algebraMap R C (counit (R := R) b) +
    (m • (toConv f.ofConv.toLinearMap - 1)).ofConv b at h
  have hn := map_nsmul (WithConv.addEquiv (B →ₗ[R] C))
    m (toConv f.ofConv.toLinearMap - 1)
  change (m • (toConv f.ofConv.toLinearMap - 1)).ofConv =
    m • (toConv f.ofConv.toLinearMap - 1).ofConv at hn
  rw [hn] at h
  simpa only [WithConv.ofConv_add, WithConv.ofConv_sub,
    WithConv.ofConv_toConv, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, AlgHom.toLinearMap_apply, LinearMap.convOne_apply,
    nsmul_eq_mul] using h

/-- There is no nontrivial m-torsion infinitesimally near the identity
when m is a unit in the test ring. -/
theorem character_eq_one_of_power_eq_one (J : Ideal C) (hJ : J ^ 2 = ⊥)
    (f : WithConv (B →ₐ[R] C))
    (hf : ∀ b, f b - algebraMap R C (counit (R := R) b) ∈ J)
    (m : ℕ) (hm : IsUnit (m : C)) (hpower : f ^ m = 1) : f = 1 := by
  ext b
  have h := character_power_apply J hJ f hf m b
  rw [hpower, AlgHom.convOne_apply] at h
  have hz : (m : C) * (f b - algebraMap R C (counit (R := R) b)) = 0 := by
    exact (add_left_cancel (h.symm.trans (add_zero _).symm))
  have hd : f b - algebraMap R C (counit (R := R) b) = 0 := by
    exact hm.mul_left_cancel (hz.trans (mul_zero _).symm)
  exact sub_eq_zero.mp hd

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.InfinitesimalEq.Infinitesimal
