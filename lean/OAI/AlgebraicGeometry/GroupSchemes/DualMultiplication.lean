import OAI.AlgebraicGeometry.GroupSchemes.Verschiebung

/-! # Dual Multiplication -/

namespace OAI.AlgebraicGeometry.GroupSchemes.DualMultiplication.FiniteEtale

noncomputable section

/-! Multiplication by p transposes under the constructed finite Cartier duality. -/

open WithConv OAI.AlgebraicGeometry.GroupSchemes.Verschiebung.FiniteEtale

universe u
variable (k A : Type u) [Field k] [CommRing A] [HopfAlgebra k A]
  [Coalgebra.IsCocomm k A] [Module.Finite k A]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

local instance : CommRing (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) := LinearMap.convCommRing
local instance : Algebra k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) := LinearMap.convAlgebra
local instance : CommRing (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A)) := LinearMap.convCommRing
local instance : Algebra k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A)) := LinearMap.convAlgebra

/-- The dual Verschiebung evaluates as the transpose of Frobenius. -/
theorem dual_verschiebung_eval_pow (f : AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) (x : A) :
    (Verschiebung.FiniteEtale.verschiebungFun p k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) f x) ^ p = f (x ^ p) := by
  have h := Verschiebung.FiniteEtale.eval_verschiebung_pow p k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A)
    (AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateBidualBialgEquiv k A x) f
  rw [← map_pow (AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateBidualBialgEquiv k A) x p] at h
  exact h

/-- The convolution pth power of the identity transposes under finite Hopf duality. -/
theorem dual_multiplication_p (f : AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) (x : A) :
    ((toConv (LinearMap.id : AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A →ₗ[k] AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A)) ^ p) f x =
      f (((toConv (LinearMap.id : A →ₗ[k] A)) ^ p) x) := by
  rw [← Verschiebung.FiniteEtale.frobenius_verschiebung p k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) f]
  rw [← Verschiebung.FiniteEtale.eval_verschiebung_pow p k A (Verschiebung.FiniteEtale.verschiebungFun p k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) f) x]
  rw [dual_verschiebung_eval_pow, Verschiebung.FiniteEtale.frobenius_verschiebung]

/-- All iterates of multiplication by p transpose as well. -/
theorem dual_multiplication_iterate (n : ℕ) (f : AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) (x : A) :
    ((((toConv (LinearMap.id : AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A →ₗ[k] AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A)) ^ p).ofConv)^[n] f) x =
      f ((((toConv (LinearMap.id : A →ₗ[k] A)) ^ p).ofConv)^[n] x) := by
  induction n generalizing f x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, dual_multiplication_p, Function.iterate_succ_apply']

end

end OAI.AlgebraicGeometry.GroupSchemes.DualMultiplication.FiniteEtale
