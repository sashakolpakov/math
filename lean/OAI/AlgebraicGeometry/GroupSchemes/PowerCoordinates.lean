import OAI.AlgebraicGeometry.GroupSchemes.CoordinatePoints
import OAI.AlgebraicGeometry.GroupSchemes.SplitAlgebra
import OAI.AlgebraicGeometry.GroupSchemes.DualMultiplication

/-! # Power Coordinates -/

namespace OAI.AlgebraicGeometry.GroupSchemes.PowerCoordinates.FiniteEtale

noncomputable section

/-! Coordinate formulas for integer multiplication and its finite Cartier dual. -/

open WithConv OAI.AlgebraicGeometry.GroupSchemes.CoordinatePoints.FiniteEtale

universe u

section Bialgebra

variable (k A : Type u) [Field k] [CommRing A] [Bialgebra k A]

/-- The coordinate endomorphism of multiplication by n. -/
def powerMap (n : ℕ) : A →ₐ[k] A := ((toConv (AlgHom.id k A)) ^ n).ofConv

theorem powerMap_one : powerMap k A 1 = AlgHom.id k A := by
  unfold powerMap
  rw [pow_one]

theorem powerMap_mul (m n : ℕ) :
    powerMap k A (m * n) = (powerMap k A m).comp (powerMap k A n) := by
  change ((toConv (AlgHom.id k A)) ^ (m * n)).ofConv =
    ((toConv (AlgHom.id k A)) ^ m).ofConv.comp ((toConv (AlgHom.id k A)) ^ n).ofConv
  rw [CoordinatePoints.FiniteEtale.comp_convolution_pow, toConv_ofConv, pow_mul]

theorem powerMap_apply (n : ℕ) (x : A) :
    powerMap k A n x = ((toConv (LinearMap.id : A →ₗ[k] A)) ^ n) x :=
  congrArg (fun f : WithConv (A →ₗ[k] A) => f x)
    (AlgHom.toLinearMap_convPow (toConv (AlgHom.id k A)) n)

/-- Prime-power multiplication is iteration of prime multiplication. -/
theorem powerMap_iterate (p n : ℕ) (x : A) :
    powerMap k A (p ^ n) x = (((toConv (LinearMap.id : A →ₗ[k] A)) ^ p).ofConv)^[n] x := by
  induction n generalizing x with
  | zero => rw [pow_zero, powerMap_one]; rfl
  | succ n ih =>
    rw [pow_succ, powerMap_mul]
    change powerMap k A (p ^ n) (powerMap k A p x) = _
    rw [ih, powerMap_apply, Function.iterate_succ_apply]

/-- For a split algebra, a power trivial on rational points is the constant-identity map. -/
theorem powerMap_constant_of_points [Algebra.IsFiniteSplit k A] (n : ℕ)
    (hpow : ∀ f : A →ₐ[k] k, (toConv f) ^ n = 1) (x : A) :
    powerMap k A n x = algebraMap k A (Coalgebra.counit (R := k) x) := by
  apply SplitAlgebra.FiniteEtale.eq_of_points k A
  intro f
  have he := congrArg (fun g : A →ₐ[k] k => g x) (CoordinatePoints.FiniteEtale.comp_convolution_pow f n)
  rw [hpow f] at he
  change f (powerMap k A n x) = Coalgebra.counit (R := k) x at he
  simpa only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using he

end Bialgebra

variable (k A : Type u) [Field k] [CommRing A] [HopfAlgebra k A]
  [Coalgebra.IsCocomm k A] [Module.Finite k A]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

local instance : CommRing (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) := LinearMap.convCommRing
local instance : Algebra k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) := LinearMap.convAlgebra

/-- Prime-power multiplication on the two finite Hopf duals is transposed. -/
theorem dual_powerMap_eval (n : ℕ) (f : AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) (x : A) :
    powerMap k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) (p ^ n) f x = f (powerMap k A (p ^ n) x) := by
  rw [powerMap_iterate, powerMap_iterate]
  exact DualMultiplication.FiniteEtale.dual_multiplication_iterate k A p n f x

/-- Trivial prime-power multiplication on the dual implies trivial multiplication on the original. -/
theorem powerMap_constant_of_dual (n : ℕ)
    (hdual : ∀ f : AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A, powerMap k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) (p ^ n) f =
      algebraMap k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) (Coalgebra.counit (R := k) f)) (x : A) :
    powerMap k A (p ^ n) x = algebraMap k A (Coalgebra.counit (R := k) x) := by
  apply (AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateBidualLinearEquiv k A).injective
  ext f
  change f (powerMap k A (p ^ n) x) = f (algebraMap k A (Coalgebra.counit (R := k) x))
  rw [← dual_powerMap_eval k A p, hdual]
  have hε : Coalgebra.counit (R := k) f = f 1 := rfl
  simp [Algebra.algebraMap_eq_smul_one, hε, mul_comm]

end

end OAI.AlgebraicGeometry.GroupSchemes.PowerCoordinates.FiniteEtale
