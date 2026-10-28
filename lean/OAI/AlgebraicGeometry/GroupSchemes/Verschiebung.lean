import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DualAlgebra
import Mathlib

/-! # Verschiebung -/

namespace OAI.AlgebraicGeometry.GroupSchemes.Verschiebung.FiniteEtale

noncomputable section

/-!
# FiniteEtale: transpose of Frobenius on a finite convolution dual

The Verschiebung map is constructed by finite-dimensional biduality. Its
evaluation formula is proved directly; no Frobenius/Verschiebung comparison
identity is assumed.
-/

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DualAlgebra.Construction WithConv

universe u v

variable (p : ℕ) [Fact p.Prime]
variable (k : Type u) [Field k] [CharP k p] [PerfectRing k p]

omit [PerfectRing k p] in
/-- The pth power is additive in every commutative k-algebra, including the zero ring. -/
theorem algebra_pow_add (B : Type*) [CommRing B] [Algebra k B] (f g : B) :
    (f + g) ^ p = f ^ p + g ^ p := by
  have hp : (p : B) = 0 := by
    rw [← map_natCast (algebraMap k B), CharP.cast_eq_zero k p, map_zero]
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : p.Prime) f g
  simpa only [hp, zero_mul, add_zero] using hr

omit [PerfectRing k p] in
/-- Frobenius commutes with finite sums in a commutative k-algebra. -/
theorem algebra_pow_sum (B : Type*) [CommRing B] [Algebra k B]
    {ι : Type*} (s : Finset ι) (f : ι → B) :
    (∑ i ∈ s, f i) ^ p = ∑ i ∈ s, (f i) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [(Fact.out : p.Prime).ne_zero]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, algebra_pow_add p k B, ih]

section Coalgebra

variable (A : Type v) [AddCommGroup A] [Module k A] [Coalgebra k A]
  [Coalgebra.IsCocomm k A] [Module.Finite k A]

local notation "D" => OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A
local notation "σ" => frobeniusEquiv k p

omit [PerfectRing k p] [Module.Finite k A] in
/-- Frobenius is additive on the convolution dual. -/
theorem dual_pow_add (f g : D) : (f + g) ^ p = f ^ p + g ^ p := by
  have hp : (p : D) = 0 := by
    rw [← map_natCast (algebraMap k D), CharP.cast_eq_zero k p, map_zero]
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : p.Prime) f g
  simpa only [hp, zero_mul, add_zero] using hr

/-- Applying inverse scalar Frobenius to evaluation of dual Frobenius is linear. -/
def rootTranspose (a : A) : Module.Dual k D where
  toFun f := (σ).symm ((f ^ p) a)
  map_add' f g := by
    rw [dual_pow_add p k A]
    exact map_add (σ).symm ((f ^ p) a) ((g ^ p) a)
  map_smul' r f := by
    rw [smul_pow]
    change (σ).symm (r ^ p * (f ^ p) a) = r * (σ).symm ((f ^ p) a)
    rw [map_mul]
    congr 1
    exact (σ).symm_apply_apply r

/-- The transpose of dual Frobenius, with the scalar twist corrected. -/
def verschiebungFun (a : A) : A :=
  (AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateBidualLinearEquiv k A).symm (toConv (rootTranspose p k A a))

/-- The defining evaluation formula follows from the proved bidual isomorphism. -/
theorem eval_verschiebung (f : D) (a : A) :
    f (verschiebungFun p k A a) = (σ).symm ((f ^ p) a) := by
  exact congrArg (fun g : AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k D => g f)
    ((AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateBidualLinearEquiv k A).apply_symm_apply (toConv (rootTranspose p k A a)))

/-- Equivalently, dual Frobenius is the pth power of evaluation on Verschiebung. -/
theorem eval_verschiebung_pow (f : D) (a : A) :
    f (verschiebungFun p k A a) ^ p = (f ^ p) a := by
  rw [eval_verschiebung]
  exact (σ).apply_symm_apply ((f ^ p) a)

/-- Verschiebung is inverse-Frobenius-semilinear. -/
def verschiebung : A →ₛₗ[(σ).symm.toRingHom] A where
  toFun := verschiebungFun p k A
  map_add' a b := by
    apply (AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateBidualLinearEquiv k A).injective
    ext f
    simp only [AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateBidualLinearEquiv_apply, map_add]
    change f (verschiebungFun p k A (a + b)) =
      f (verschiebungFun p k A a) + f (verschiebungFun p k A b)
    rw [eval_verschiebung, eval_verschiebung, eval_verschiebung]
    simp only [map_add]
  map_smul' r a := by
    apply (AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateBidualLinearEquiv k A).injective
    ext f
    simp only [AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateBidualLinearEquiv_apply, map_smul]
    change f (verschiebungFun p k A (r • a)) =
      (σ).symm r * f (verschiebungFun p k A a)
    rw [eval_verschiebung, eval_verschiebung]
    simp only [map_smul, smul_eq_mul, map_mul]

end Coalgebra

open scoped TensorProduct

variable (A : Type v) [CommRing A] [HopfAlgebra k A]
  [Coalgebra.IsCocomm k A] [Module.Finite k A]

local notation "D" => OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A
local notation "σ" => frobeniusEquiv k p

local instance : CommRing D := LinearMap.convCommRing
local instance : Algebra k D := LinearMap.convAlgebra
local instance : CommRing (D ⊗[k] D) := Algebra.TensorProduct.instCommRing

/-- Evaluation of tensor Frobenius against two vectors is expressed by Verschiebung. -/
theorem tensor_eval_pow (t : D ⊗[k] D) (x y : A) :
    AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateTensorEquiv k A A (t ^ p) (x ⊗ₜ[k] y) =
      (AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateTensorEquiv k A A t
        (verschiebungFun p k A x ⊗ₜ[k] verschiebungFun p k A y)) ^ p := by
  induction t using TensorProduct.inductionOn with
  | tmul f g =>
      rw [Algebra.TensorProduct.tmul_pow, AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateTensorEquiv_apply,
        AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateTensorEquiv_apply, mul_pow,
        eval_verschiebung_pow, eval_verschiebung_pow]
  | add a b ha hb =>
      rw [algebra_pow_add p k (D ⊗[k] D), map_add, LinearMap.add_apply,
        map_add, LinearMap.add_apply, algebra_pow_add p k k, ha, hb]

/-- The constructed Verschiebung preserves multiplication in the coordinate algebra. -/
theorem verschiebung_mul (x y : A) :
    verschiebungFun p k A (x * y) =
      verschiebungFun p k A x * verschiebungFun p k A y := by
  apply (AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateBidualLinearEquiv k A).injective
  ext f
  simp only [AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateBidualLinearEquiv_apply]
  apply (σ).injective
  change f (verschiebungFun p k A (x * y)) ^ p =
    f (verschiebungFun p k A x * verschiebungFun p k A y) ^ p
  rw [eval_verschiebung_pow]
  calc
    (f ^ p) (x * y) = AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateTensorEquiv k A A
        (AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateComul k A (f ^ p)) (x ⊗ₜ[k] y) :=
      (AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateComul_apply k A _ _ _).symm
    _ = AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateTensorEquiv k A A
        ((AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateComul k A f) ^ p) (x ⊗ₜ[k] y) := by
      congr 2
      exact Bialgebra.comul_pow f p
    _ = _ := by rw [tensor_eval_pow, AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateComul_apply]

/-- The constructed Verschiebung preserves the multiplicative identity. -/
theorem verschiebung_one : verschiebungFun p k A 1 = 1 := by
  apply (AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateBidualLinearEquiv k A).injective
  ext f
  simp only [AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateBidualLinearEquiv_apply]
  apply (σ).injective
  change f (verschiebungFun p k A 1) ^ p = f 1 ^ p
  rw [eval_verschiebung_pow]
  exact Bialgebra.counit_pow f p

/-- Verschiebung is an actual ring map; its scalar action is inverse Frobenius. -/
def verschiebungRingHom : A →+* A where
  __ := (verschiebung p k A).toAddMonoidHom
  map_one' := verschiebung_one p k A
  map_mul' := verschiebung_mul p k A

/-- Rank-one linear maps are used to expand the convolution identity. -/
def rankOne (f : D) (a : A) : WithConv (A →ₗ[k] A) :=
  toConv (f.ofConv.smulRight a)

omit [Coalgebra.IsCocomm k A] [Module.Finite k A] in
theorem rankOne_pow_apply (f : D) (a x : A) (n : ℕ) :
    (rankOne k A f a ^ n) x = (f ^ n) x • a ^ n := by
  induction n generalizing x with
  | zero =>
      simp only [pow_zero, LinearMap.convOne_apply, Algebra.smul_def, mul_one]
      rfl
  | succ n ih =>
      rw [pow_succ, (Coalgebra.Repr.arbitrary k x).convMul_apply]
      simp_rw [ih]
      simp only [rankOne, LinearMap.smulRight_apply]
      rw [pow_succ, (Coalgebra.Repr.arbitrary k x).convMul_apply, pow_succ]
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Algebra.smul_def, map_mul]
      ring

omit [Coalgebra.IsCocomm k A] [Module.Finite k A] in
/-- The convolution identity has the usual finite basis expansion. -/
theorem identity_eq_sum_rankOne {ι : Type*} [Fintype ι] (b : Module.Basis ι k A) :
    (toConv (LinearMap.id : A →ₗ[k] A)) =
      ∑ i, rankOne k A (toConv (b.coord i)) (b i) := by
  ext x
  simp only [WithConv.ofConv_sum, LinearMap.sum_apply, rankOne, LinearMap.smulRight_apply]
  exact (b.sum_repr x).symm

/-- Frobenius after the constructed Verschiebung is multiplication by p in the
coordinate Hopf algebra, whose comorphism is the pth convolution power of the identity. -/
theorem frobenius_verschiebung (x : A) :
    verschiebungFun p k A x ^ p =
      ((toConv (LinearMap.id : A →ₗ[k] A)) ^ p) x := by
  let b := Module.finBasis k A
  rw [identity_eq_sum_rankOne k A b, algebra_pow_sum p k (WithConv (A →ₗ[k] A))]
  have hx := b.sum_repr (verschiebungFun p k A x)
  rw [← hx, algebra_pow_sum p k A]
  simp only [WithConv.ofConv_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_pow, rankOne_pow_apply]
  congr 1
  exact eval_verschiebung_pow p k A (toConv (b.coord i)) x

/-- The reverse composite is also multiplication by p. -/
theorem verschiebung_frobenius (x : A) :
    verschiebungFun p k A (x ^ p) =
      ((toConv (LinearMap.id : A →ₗ[k] A)) ^ p) x := by
  rw [← frobenius_verschiebung p k A x]
  exact (verschiebungRingHom p k A).map_pow x p

end

end OAI.AlgebraicGeometry.GroupSchemes.Verschiebung.FiniteEtale
