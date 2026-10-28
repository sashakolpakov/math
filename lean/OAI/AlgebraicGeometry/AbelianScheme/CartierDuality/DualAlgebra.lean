import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.TensorProduct
import Mathlib.RingTheory.Bialgebra.Equiv
import Mathlib.RingTheory.HopfAlgebra.GroupLike
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Dual Algebra -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DualAlgebra.Construction

noncomputable section

/-!
# CartierDuality: dual coordinate algebras

Result-specific foundations for Cartier duality. These constructions use
finite projective modules over arbitrary commutative rings, so no assumption
on the residue characteristic or a global choice of basis is made.
This file does not import the statement schema or other project results.
-/

open _root_.Module TensorProduct Coalgebra

universe u v w

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]
variable (N : Type w) [AddCommGroup N] [Module R N]

/-- The underlying module of the dual coordinate algebra. The type synonym
reserves multiplication for convolution, rather than composition. -/
abbrev DualCoordinate := WithConv (Module.Dual R M)

/-- The ordinary dual and the convolution dual have identical linear data. -/
def dualCoordinateLinearEquiv : DualCoordinate R M ≃ₗ[R] Module.Dual R M :=
  WithConv.linearEquiv R _

instance dualCoordinate_finite [Module.Finite R M] [Module.Projective R M] :
    Module.Finite R (DualCoordinate R M) :=
  Module.Finite.equiv (dualCoordinateLinearEquiv R M).symm

instance dualCoordinate_projective [Module.Finite R M] [Module.Projective R M] :
    Module.Projective R (DualCoordinate R M) :=
  Module.Projective.of_equiv (dualCoordinateLinearEquiv R M).symm

variable [Module.Finite R M] [Module.Projective R M]
variable [Module.Finite R N] [Module.Projective R N]

/-- Evaluation identifies a finite projective module with its double dual. -/
def dualCoordinateBidualLinearEquiv :
    M ≃ₗ[R] DualCoordinate R (DualCoordinate R M) :=
  Module.evalEquiv R M ≪≫ₗ (dualCoordinateLinearEquiv R M).dualMap ≪≫ₗ
    (dualCoordinateLinearEquiv R (DualCoordinate R M)).symm

@[simp]
theorem dualCoordinateBidualLinearEquiv_apply (x : M) (f : DualCoordinate R M) :
    dualCoordinateBidualLinearEquiv R M x f = f x := rfl

/-- Tensor duality for finite projective modules, without choosing bases. -/
def finiteProjectiveDualTensorEquiv :
    Module.Dual R M ⊗[R] Module.Dual R N ≃ₗ[R] Module.Dual R (M ⊗[R] N) :=
  homTensorHomEquiv R M N R R ≪≫ₗ
    LinearEquiv.congrRight (TensorProduct.lid R R)

@[simp]
theorem finiteProjectiveDualTensorEquiv_apply
    (f : Module.Dual R M) (g : Module.Dual R N) (x : M) (y : N) :
    finiteProjectiveDualTensorEquiv R M N (f ⊗ₜ[R] g) (x ⊗ₜ[R] y) =
      f x * g y := by
  simp only [finiteProjectiveDualTensorEquiv, LinearEquiv.trans_apply,
    homTensorHomEquiv_apply, homTensorHomMap_apply]
  rfl

/-- The same tensor duality with convolution type synonyms. -/
def dualCoordinateTensorEquiv :
    DualCoordinate R M ⊗[R] DualCoordinate R N ≃ₗ[R]
      Module.Dual R (M ⊗[R] N) :=
  TensorProduct.congr (dualCoordinateLinearEquiv R M)
    (dualCoordinateLinearEquiv R N) ≪≫ₗ
      finiteProjectiveDualTensorEquiv R M N

@[simp]
theorem dualCoordinateTensorEquiv_apply
    (f : DualCoordinate R M) (g : DualCoordinate R N) (x : M) (y : N) :
    dualCoordinateTensorEquiv R M N (f ⊗ₜ[R] g) (x ⊗ₜ[R] y) =
      f x * g y := by
  simp [dualCoordinateTensorEquiv, dualCoordinateLinearEquiv]

/-- Pure test vectors detect equality in the tensor of the dual modules. -/
theorem dualCoordinateTensor_ext
    {a b : DualCoordinate R M ⊗[R] DualCoordinate R N}
    (h : ∀ (x : M) (y : N),
      dualCoordinateTensorEquiv R M N a (x ⊗ₜ[R] y) =
        dualCoordinateTensorEquiv R M N b (x ⊗ₜ[R] y)) : a = b := by
  apply (dualCoordinateTensorEquiv R M N).injective
  ext x y
  exact h x y

section AlgebraDual

variable (A : Type v) [CommRing A] [Algebra R A]
variable [Module.Finite R A] [Module.Projective R A]

/-- The transpose of multiplication, using finite projectivity to express
the resulting bilinear form as a tensor of dual elements. -/
def dualCoordinateComul : DualCoordinate R A →ₗ[R]
    DualCoordinate R A ⊗[R] DualCoordinate R A :=
  (dualCoordinateTensorEquiv R A A).symm.toLinearMap ∘ₗ
    (LinearMap.mul' R A).dualMap ∘ₗ
      (dualCoordinateLinearEquiv R A).toLinearMap

/-- The transpose of the unit. -/
def dualCoordinateCounit : DualCoordinate R A →ₗ[R] R :=
  (Module.Dual.eval R A 1) ∘ₗ
    (dualCoordinateLinearEquiv R A).toLinearMap

omit [Module.Finite R A] [Module.Projective R A] in
@[simp]
theorem dualCoordinateCounit_apply (f : DualCoordinate R A) :
    dualCoordinateCounit R A f = f 1 := rfl

@[simp]
theorem dualCoordinateComul_apply (f : DualCoordinate R A) (x y : A) :
    dualCoordinateTensorEquiv R A A (dualCoordinateComul R A f)
      (x ⊗ₜ[R] y) = f (x * y) := by
  simp [dualCoordinateComul, dualCoordinateLinearEquiv]

@[simp]
theorem dualCoordinateComul_eval (f : DualCoordinate R A) (t : A ⊗[R] A) :
    dualCoordinateTensorEquiv R A A (dualCoordinateComul R A f) t =
      f (LinearMap.mul' R A t) := by
  simp [dualCoordinateComul, dualCoordinateLinearEquiv]

/-- Tensor duality in three variables, with the left-associated convention. -/
def dualCoordinateTripleEquiv :
    (DualCoordinate R A ⊗[R] DualCoordinate R A) ⊗[R] DualCoordinate R A ≃ₗ[R]
      Module.Dual R ((A ⊗[R] A) ⊗[R] A) :=
  TensorProduct.congr (dualCoordinateTensorEquiv R A A)
    (dualCoordinateLinearEquiv R A) ≪≫ₗ
      finiteProjectiveDualTensorEquiv R (A ⊗[R] A) A

@[simp]
theorem dualCoordinateTripleEquiv_tmul
    (t : DualCoordinate R A ⊗[R] DualCoordinate R A)
    (f : DualCoordinate R A) (x y z : A) :
    dualCoordinateTripleEquiv R A (t ⊗ₜ[R] f) ((x ⊗ₜ[R] y) ⊗ₜ[R] z) =
      dualCoordinateTensorEquiv R A A t (x ⊗ₜ[R] y) * f z := by
  simp [dualCoordinateTripleEquiv, dualCoordinateLinearEquiv]

theorem dualCoordinateTriple_ext
    {a b : (DualCoordinate R A ⊗[R] DualCoordinate R A) ⊗[R] DualCoordinate R A}
    (h : ∀ x y z : A,
      dualCoordinateTripleEquiv R A a ((x ⊗ₜ[R] y) ⊗ₜ[R] z) =
        dualCoordinateTripleEquiv R A b ((x ⊗ₜ[R] y) ⊗ₜ[R] z)) : a = b := by
  apply (dualCoordinateTripleEquiv R A).injective
  ext x y z
  exact h x y z

theorem dualCoordinateTriple_comul_left
    (t : DualCoordinate R A ⊗[R] DualCoordinate R A) (x y z : A) :
    dualCoordinateTripleEquiv R A
      ((dualCoordinateComul R A).rTensor (DualCoordinate R A) t)
      ((x ⊗ₜ[R] y) ⊗ₜ[R] z) =
        dualCoordinateTensorEquiv R A A t ((x * y) ⊗ₜ[R] z) := by
  induction t using TensorProduct.inductionOn with
  | tmul f g => simp
  | add a b ha hb => simp [ha, hb]

theorem dualCoordinateTriple_comul_right
    (t : DualCoordinate R A ⊗[R] DualCoordinate R A) (x y z : A) :
    dualCoordinateTripleEquiv R A
      ((TensorProduct.assoc R (DualCoordinate R A) (DualCoordinate R A)
        (DualCoordinate R A)).symm
          ((dualCoordinateComul R A).lTensor (DualCoordinate R A) t))
      ((x ⊗ₜ[R] y) ⊗ₜ[R] z) =
        dualCoordinateTensorEquiv R A A t (x ⊗ₜ[R] (y * z)) := by
  have htmul (f : DualCoordinate R A)
      (s : DualCoordinate R A ⊗[R] DualCoordinate R A) :
      dualCoordinateTripleEquiv R A
        ((TensorProduct.assoc R (DualCoordinate R A) (DualCoordinate R A)
          (DualCoordinate R A)).symm (f ⊗ₜ[R] s))
        ((x ⊗ₜ[R] y) ⊗ₜ[R] z) =
          f x * dualCoordinateTensorEquiv R A A s (y ⊗ₜ[R] z) := by
    induction s using TensorProduct.inductionOn with
    | tmul g h => simp [mul_assoc]
    | add a b ha hb => simp [tmul_add, ha, hb, mul_add]
  induction t using TensorProduct.inductionOn with
  | tmul f g => simp [htmul]
  | add a b ha hb => simp [ha, hb]

theorem dualCoordinateComul_coassoc :
    (TensorProduct.assoc R (DualCoordinate R A) (DualCoordinate R A)
      (DualCoordinate R A)).toLinearMap ∘ₗ
      (dualCoordinateComul R A).rTensor (DualCoordinate R A) ∘ₗ
        dualCoordinateComul R A =
    (dualCoordinateComul R A).lTensor (DualCoordinate R A) ∘ₗ
      dualCoordinateComul R A := by
  apply LinearMap.ext
  intro f
  apply (TensorProduct.assoc R (DualCoordinate R A) (DualCoordinate R A)
    (DualCoordinate R A)).symm.injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  apply dualCoordinateTriple_ext
  intro x y z
  rw [dualCoordinateTriple_comul_left, dualCoordinateTriple_comul_right]
  simp [mul_assoc]

theorem dualCoordinateTensor_counit_left
    (t : DualCoordinate R A ⊗[R] DualCoordinate R A) (x : A) :
    dualCoordinateLinearEquiv R A
      (TensorProduct.lid R (DualCoordinate R A)
        ((dualCoordinateCounit R A).rTensor (DualCoordinate R A) t)) x =
      dualCoordinateTensorEquiv R A A t (1 ⊗ₜ[R] x) := by
  induction t using TensorProduct.inductionOn with
  | tmul f g => simp [dualCoordinateLinearEquiv]
  | add a b ha hb => simp [ha, hb]

theorem dualCoordinateTensor_counit_right
    (t : DualCoordinate R A ⊗[R] DualCoordinate R A) (x : A) :
    dualCoordinateLinearEquiv R A
      (TensorProduct.rid R (DualCoordinate R A)
        ((dualCoordinateCounit R A).lTensor (DualCoordinate R A) t)) x =
      dualCoordinateTensorEquiv R A A t (x ⊗ₜ[R] 1) := by
  induction t using TensorProduct.inductionOn with
  | tmul f g => simp [dualCoordinateLinearEquiv, mul_comm]
  | add a b ha hb => simp [ha, hb]

/-- A finite projective commutative algebra has a canonical dual coalgebra. -/
instance dualCoordinateCoalgebra : Coalgebra R (DualCoordinate R A) where
  comul := dualCoordinateComul R A
  counit := dualCoordinateCounit R A
  coassoc := dualCoordinateComul_coassoc R A
  rTensor_counit_comp_comul := by
    apply LinearMap.ext
    intro f
    apply (TensorProduct.lid R (DualCoordinate R A)).injective
    apply (dualCoordinateLinearEquiv R A).injective
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, TensorProduct.mk_apply, TensorProduct.lid_tmul,
      one_smul]
    rw [dualCoordinateTensor_counit_left, dualCoordinateComul_apply]
    simp [dualCoordinateLinearEquiv]
  lTensor_counit_comp_comul := by
    apply LinearMap.ext
    intro f
    apply (TensorProduct.rid R (DualCoordinate R A)).injective
    apply (dualCoordinateLinearEquiv R A).injective
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
      TensorProduct.rid_tmul, one_smul]
    rw [dualCoordinateTensor_counit_right, dualCoordinateComul_apply]
    simp [dualCoordinateLinearEquiv]

theorem dualCoordinateTensor_comm
    (t : DualCoordinate R A ⊗[R] DualCoordinate R A) (x y : A) :
    dualCoordinateTensorEquiv R A A
      (TensorProduct.comm R (DualCoordinate R A) (DualCoordinate R A) t)
      (x ⊗ₜ[R] y) =
        dualCoordinateTensorEquiv R A A t (y ⊗ₜ[R] x) := by
  induction t using TensorProduct.inductionOn with
  | tmul f g => simp [mul_comm]
  | add a b ha hb => simp [ha, hb]

/-- The dual coalgebra is cocommutative because the original multiplication
is commutative. -/
instance dualCoordinateIsCocomm : Coalgebra.IsCocomm R (DualCoordinate R A) where
  comm_comp_comul := by
    apply LinearMap.ext
    intro f
    apply dualCoordinateTensor_ext
    intro x y
    change dualCoordinateTensorEquiv R A A
      (TensorProduct.comm R (DualCoordinate R A) (DualCoordinate R A)
        (dualCoordinateComul R A f)) (x ⊗ₜ[R] y) =
      dualCoordinateTensorEquiv R A A (dualCoordinateComul R A f) (x ⊗ₜ[R] y)
    rw [dualCoordinateTensor_comm]
    simp [mul_comm]

/-- A group-like functional is exactly a unital algebra homomorphism. -/
def groupLikeDualEquivAlgHom : GroupLike R (DualCoordinate R A) ≃ (A →ₐ[R] R) where
  toFun f := AlgHom.ofLinearMap f.val.ofConv
    f.isGroupLikeElem_val.counit_eq_one (by
      intro x y
      have h := congrArg
        (fun t => dualCoordinateTensorEquiv R A A t (x ⊗ₜ[R] y))
        f.isGroupLikeElem_val.comul_eq_tmul_self
      change dualCoordinateTensorEquiv R A A (dualCoordinateComul R A f.val)
        (x ⊗ₜ[R] y) = _ at h
      simpa only [dualCoordinateComul_apply, dualCoordinateTensorEquiv_apply] using h)
  invFun f := ⟨WithConv.toConv f.toLinearMap, {
    counit_eq_one := f.map_one
    comul_eq_tmul_self := by
      apply dualCoordinateTensor_ext
      intro x y
      change dualCoordinateTensorEquiv R A A
        (dualCoordinateComul R A (WithConv.toConv f.toLinearMap)) (x ⊗ₜ[R] y) = _
      simp }⟩
  left_inv f := by apply GroupLike.val_injective; rfl
  right_inv f := by ext x; rfl

end AlgebraDual

section BialgebraDual

variable (A : Type v) [CommRing A] [Bialgebra R A] [Coalgebra.IsCocomm R A]
variable [Module.Finite R A] [Module.Projective R A]

local instance : CommRing (DualCoordinate R A) := LinearMap.convCommRing
local instance : Algebra R (DualCoordinate R A) := LinearMap.convAlgebra
local instance : CommRing (DualCoordinate R A ⊗[R] DualCoordinate R A) :=
  Algebra.TensorProduct.instCommRing

theorem dualCoordinateTensor_mul
    (a b : DualCoordinate R A ⊗[R] DualCoordinate R A) :
    WithConv.toConv (dualCoordinateTensorEquiv R A A (a * b)) =
      WithConv.toConv (dualCoordinateTensorEquiv R A A a) *
        WithConv.toConv (dualCoordinateTensorEquiv R A A b) := by
  induction a using TensorProduct.inductionOn with
  | add a₁ a₂ ha₁ ha₂ =>
    rw [add_mul, map_add, WithConv.toConv_add, ha₁, ha₂, map_add,
      WithConv.toConv_add, add_mul]
  | tmul f g =>
    induction b using TensorProduct.inductionOn with
    | add b₁ b₂ hb₁ hb₂ =>
      rw [mul_add, map_add, WithConv.toConv_add, hb₁, hb₂, map_add,
        WithConv.toConv_add, mul_add]
    | tmul h k =>
      apply WithConv.ext
      ext x y
      change dualCoordinateTensorEquiv R A A
        ((f ⊗ₜ[R] g) * (h ⊗ₜ[R] k)) (x ⊗ₜ[R] y) =
          (WithConv.toConv (dualCoordinateTensorEquiv R A A (f ⊗ₜ[R] g)) *
            WithConv.toConv (dualCoordinateTensorEquiv R A A (h ⊗ₜ[R] k)))
              (x ⊗ₜ[R] y)
      rw [Algebra.TensorProduct.tmul_mul_tmul, dualCoordinateTensorEquiv_apply]
      rw [(Coalgebra.Repr.arbitrary R x).convMul_apply,
        (Coalgebra.Repr.arbitrary R y).convMul_apply,
        ((Coalgebra.Repr.arbitrary R x).tmul
          (Coalgebra.Repr.arbitrary R y)).convMul_apply]
      simp [Finset.sum_mul_sum, mul_mul_mul_comm, Finset.sum_product]

theorem dualCoordinateComul_mul (f g : DualCoordinate R A) :
    dualCoordinateComul R A (f * g) =
      dualCoordinateComul R A f * dualCoordinateComul R A g := by
  apply (dualCoordinateTensorEquiv R A A).injective
  apply WithConv.toConv_injective
  rw [dualCoordinateTensor_mul]
  have h (a : DualCoordinate R A) :
      dualCoordinateTensorEquiv R A A (dualCoordinateComul R A a) =
        a.ofConv.comp (Bialgebra.mulCoalgHom R A).toLinearMap := by
    ext x y
    simp
  rw [h, h, h, LinearMap.convMul_comp_coalgHom_distrib]

omit [Coalgebra.IsCocomm R A] in
theorem dualCoordinateComul_one :
    dualCoordinateComul R A (1 : DualCoordinate R A) = 1 := by
  apply dualCoordinateTensor_ext
  intro x y
  rw [dualCoordinateComul_apply, Algebra.TensorProduct.one_def,
    dualCoordinateTensorEquiv_apply]
  simp

/-- The convolution algebra and transposed algebra operations satisfy all
bialgebra laws. -/
instance dualCoordinateBialgebra : Bialgebra R (DualCoordinate R A) :=
  Bialgebra.mk' R (DualCoordinate R A)
    (by change (1 : DualCoordinate R A) 1 = 1; simp)
    (by
      intro f g
      change (f * g) 1 = f 1 * g 1
      simp [LinearMap.convMul_apply, Algebra.TensorProduct.one_def])
    (dualCoordinateComul_one R A)
    (fun {f g} => dualCoordinateComul_mul R A f g)

omit [Coalgebra.IsCocomm R A] in
theorem dualCoordinateMultiply_apply
    (t : DualCoordinate R A ⊗[R] DualCoordinate R A) (x : A) :
    (LinearMap.mul' R (DualCoordinate R A) t) x =
      dualCoordinateTensorEquiv R A A t (Coalgebra.comul x) := by
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simp [ha, hb]
  | tmul f g =>
    change (f * g) x = _
    rw [LinearMap.convMul_apply]
    have h (z : A ⊗[R] A) :
        LinearMap.mul' R R (TensorProduct.map f.ofConv g.ofConv z) =
          dualCoordinateTensorEquiv R A A (f ⊗ₜ[R] g) z := by
      induction z using TensorProduct.inductionOn with
      | tmul a b => simp
      | add a b ha hb => simp [ha, hb]
    exact h _

omit [Coalgebra.IsCocomm R A] in
theorem dualCoordinateBidual_tensor_evaluation
    (t : DualCoordinate R A ⊗[R] DualCoordinate R A) (x y : A) :
    LinearMap.mul' R R
      (TensorProduct.map (dualCoordinateBidualLinearEquiv R A x).ofConv
        (dualCoordinateBidualLinearEquiv R A y).ofConv t) =
      dualCoordinateTensorEquiv R A A t (x ⊗ₜ[R] y) := by
  induction t using TensorProduct.inductionOn with
  | tmul f g => simp
  | add a b ha hb => simp [ha, hb]

omit [Coalgebra.IsCocomm R A] in
theorem dualCoordinateBidual_mul (x y : A) :
    dualCoordinateBidualLinearEquiv R A (x * y) =
      dualCoordinateBidualLinearEquiv R A x *
        dualCoordinateBidualLinearEquiv R A y := by
  apply WithConv.ext
  apply LinearMap.ext
  intro f
  change f (x * y) =
    (dualCoordinateBidualLinearEquiv R A x *
      dualCoordinateBidualLinearEquiv R A y) f
  rw [LinearMap.convMul_apply, dualCoordinateBidual_tensor_evaluation]
  exact (dualCoordinateComul_apply R A f x y).symm

omit [Coalgebra.IsCocomm R A] in
theorem dualCoordinateBidual_map_evaluation
    (t : A ⊗[R] A) (f g : DualCoordinate R A) :
    dualCoordinateTensorEquiv R (DualCoordinate R A) (DualCoordinate R A)
      (TensorProduct.map (dualCoordinateBidualLinearEquiv R A).toLinearMap
        (dualCoordinateBidualLinearEquiv R A).toLinearMap t) (f ⊗ₜ[R] g) =
      LinearMap.mul' R R (TensorProduct.map f.ofConv g.ofConv t) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [TensorProduct.map_tmul, dualCoordinateTensorEquiv_apply,
      LinearEquiv.coe_coe, dualCoordinateBidualLinearEquiv_apply]
    rfl
  | add a b ha hb =>
    simp only [LinearMap.map_add, LinearEquiv.map_add, LinearMap.add_apply, ha, hb]

/-- Bidual evaluation is an isomorphism of bialgebras, not just of modules. -/
def dualCoordinateBidualBialgEquiv :
    A ≃ₐc[R] DualCoordinate R (DualCoordinate R A) where
  __ := dualCoordinateBidualLinearEquiv R A
  map_mul' := dualCoordinateBidual_mul R A
  counit_comp := by
    apply LinearMap.ext
    intro x
    change dualCoordinateBidualLinearEquiv R A x (1 : DualCoordinate R A) =
      Coalgebra.counit x
    simp
  map_comp_comul := by
    apply LinearMap.ext
    intro x
    apply dualCoordinateTensor_ext
    intro f g
    change dualCoordinateTensorEquiv R (DualCoordinate R A) (DualCoordinate R A)
      (TensorProduct.map (dualCoordinateBidualLinearEquiv R A).toLinearMap
        (dualCoordinateBidualLinearEquiv R A).toLinearMap (Coalgebra.comul x))
          (f ⊗ₜ[R] g) =
      dualCoordinateTensorEquiv R (DualCoordinate R A) (DualCoordinate R A)
        (dualCoordinateComul R (DualCoordinate R A)
          (dualCoordinateBidualLinearEquiv R A x)) (f ⊗ₜ[R] g)
    rw [dualCoordinateBidual_map_evaluation, dualCoordinateComul_apply]
    rfl

end BialgebraDual

section HopfDual

variable (A : Type v) [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
variable [Module.Finite R A] [Module.Projective R A]

local instance : CommRing (DualCoordinate R A) := LinearMap.convCommRing
local instance : Algebra R (DualCoordinate R A) := LinearMap.convAlgebra
local instance : CommRing (DualCoordinate R A ⊗[R] DualCoordinate R A) :=
  Algebra.TensorProduct.instCommRing

/-- The antipode of the dual is the transpose of the original antipode. -/
def dualCoordinateAntipode : DualCoordinate R A →ₗ[R] DualCoordinate R A :=
  (dualCoordinateLinearEquiv R A).symm.toLinearMap ∘ₗ
    (HopfAlgebra.antipode R).dualMap ∘ₗ
      (dualCoordinateLinearEquiv R A).toLinearMap

omit [Module.Finite R A] [Module.Projective R A] [Coalgebra.IsCocomm R A] in
@[simp]
theorem dualCoordinateAntipode_apply (f : DualCoordinate R A) (x : A) :
    dualCoordinateAntipode R A f x = f (HopfAlgebra.antipode R x) := rfl

omit [Coalgebra.IsCocomm R A] in
theorem dualCoordinateTensor_antipode_left
    (t : DualCoordinate R A ⊗[R] DualCoordinate R A) (z : A ⊗[R] A) :
    dualCoordinateTensorEquiv R A A
      ((dualCoordinateAntipode R A).rTensor (DualCoordinate R A) t) z =
    dualCoordinateTensorEquiv R A A t
      ((HopfAlgebra.antipode R).rTensor A z) := by
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simp [ha, hb]
  | tmul f g =>
    induction z using TensorProduct.inductionOn with
    | tmul x y => simp
    | add a b ha hb => simp only [map_add, ha, hb]

omit [Coalgebra.IsCocomm R A] in
theorem dualCoordinateTensor_antipode_right
    (t : DualCoordinate R A ⊗[R] DualCoordinate R A) (z : A ⊗[R] A) :
    dualCoordinateTensorEquiv R A A
      ((dualCoordinateAntipode R A).lTensor (DualCoordinate R A) t) z =
    dualCoordinateTensorEquiv R A A t
      ((HopfAlgebra.antipode R).lTensor A z) := by
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simp [ha, hb]
  | tmul f g =>
    induction z using TensorProduct.inductionOn with
    | tmul x y => simp
    | add a b ha hb => simp only [map_add, ha, hb]

/-- The linear dual of a finite projective commutative, cocommutative Hopf
algebra is again such a Hopf algebra. All structure laws are proved. -/
instance dualCoordinateHopfAlgebra : HopfAlgebra R (DualCoordinate R A) where
  antipode := dualCoordinateAntipode R A
  mul_antipode_rTensor_comul := by
    apply LinearMap.ext
    intro f
    apply WithConv.ext
    apply LinearMap.ext
    intro x
    change (LinearMap.mul' R (DualCoordinate R A)
      ((dualCoordinateAntipode R A).rTensor (DualCoordinate R A)
        (dualCoordinateComul R A f))) x =
      (algebraMap R (DualCoordinate R A) (f 1)) x
    rw [dualCoordinateMultiply_apply, dualCoordinateTensor_antipode_left,
      dualCoordinateComul_eval, HopfAlgebra.mul_antipode_rTensor_comul_apply]
    simp [Algebra.algebraMap_eq_smul_one, mul_comm]
  mul_antipode_lTensor_comul := by
    apply LinearMap.ext
    intro f
    apply WithConv.ext
    apply LinearMap.ext
    intro x
    change (LinearMap.mul' R (DualCoordinate R A)
      ((dualCoordinateAntipode R A).lTensor (DualCoordinate R A)
        (dualCoordinateComul R A f))) x =
      (algebraMap R (DualCoordinate R A) (f 1)) x
    rw [dualCoordinateMultiply_apply, dualCoordinateTensor_antipode_right,
      dualCoordinateComul_eval, HopfAlgebra.mul_antipode_lTensor_comul_apply]
    simp [Algebra.algebraMap_eq_smul_one, mul_comm]

end HopfDual

section BaseChange

variable (S : Type w) [CommRing S] [Algebra R S]

/-- The canonical map from the base change of the linear dual to the dual
of the base change. It is defined without a freeness or flatness hypothesis. -/
def dualModuleBaseChangeMap :
    S ⊗[R] Module.Dual R M →ₗ[S] Module.Dual S (S ⊗[R] M) :=
  (Module.Dual.baseChange (R := R) (V := M) S).liftBaseChange S

omit [Module.Finite R M] [Module.Projective R M] in
@[simp]
theorem dualModuleBaseChangeMap_apply
    (s t : S) (f : Module.Dual R M) (x : M) :
    dualModuleBaseChangeMap R M S (s ⊗ₜ[R] f) (t ⊗ₜ[R] x) =
      s * t * algebraMap R S (f x) := by
  simp [dualModuleBaseChangeMap, Algebra.smul_def, mul_comm, mul_assoc]

/-- Tensor-Hom adjunction supplies the inverse at the level of R-modules. -/
def dualModuleBaseChangeAux :
    S ⊗[R] Module.Dual R M ≃ₗ[R] Module.Dual S (S ⊗[R] M) :=
  TensorProduct.comm R S (Module.Dual R M) ≪≫ₗ
    dualTensorHomEquiv R M S ≪≫ₗ
      (LinearMap.liftBaseChangeEquiv S).restrictScalars R

theorem dualModuleBaseChangeMap_eq :
    (dualModuleBaseChangeMap R M S).restrictScalars R =
      (dualModuleBaseChangeAux R M S).toLinearMap := by
  ext s f x
  simp [dualModuleBaseChangeAux, dualModuleBaseChangeMap,
    dualTensorHomEquiv, Algebra.smul_def, mul_comm, mul_left_comm]

/-- Finite projective linear duality commutes with arbitrary scalar extension.
No flatness of the base-change algebra is needed. -/
def finiteProjectiveDualBaseChangeEquiv :
    S ⊗[R] Module.Dual R M ≃ₗ[S] Module.Dual S (S ⊗[R] M) :=
  LinearEquiv.ofBijective (dualModuleBaseChangeMap R M S) (by
    change Function.Bijective ((dualModuleBaseChangeMap R M S).restrictScalars R)
    rw [dualModuleBaseChangeMap_eq]
    exact (dualModuleBaseChangeAux R M S).bijective)

@[simp]
theorem finiteProjectiveDualBaseChangeEquiv_apply
    (s t : S) (f : Module.Dual R M) (x : M) :
    finiteProjectiveDualBaseChangeEquiv R M S (s ⊗ₜ[R] f) (t ⊗ₜ[R] x) =
      s * t * algebraMap R S (f x) :=
  dualModuleBaseChangeMap_apply R M S s t f x

/-- Base change for the convolution dual, with its scalar-linear structure. -/
def dualCoordinateBaseChangeLinearEquiv :
    S ⊗[R] DualCoordinate R M ≃ₗ[S] DualCoordinate S (S ⊗[R] M) :=
  (dualCoordinateLinearEquiv R M).baseChange R S _ _ ≪≫ₗ
    finiteProjectiveDualBaseChangeEquiv R M S ≪≫ₗ
      (dualCoordinateLinearEquiv S (S ⊗[R] M)).symm

@[simp]
theorem dualCoordinateBaseChangeLinearEquiv_apply
    (s t : S) (f : DualCoordinate R M) (x : M) :
    dualCoordinateBaseChangeLinearEquiv R M S (s ⊗ₜ[R] f) (t ⊗ₜ[R] x) =
      s * t * algebraMap R S (f x) := by
  simp [dualCoordinateBaseChangeLinearEquiv, dualCoordinateLinearEquiv]

end BaseChange

section CoalgebraBaseChange

variable (S : Type w) [CommRing S] [Algebra R S]
variable (C : Type v) [AddCommGroup C] [Module R C] [Coalgebra R C]

/-- A concrete comultiplication expansion survives arbitrary base change. -/
def scalarExtensionRepr {x : C} {ι : Type*} (ρ : Coalgebra.Repr R x ι) (s : S) :
    Coalgebra.Repr S (s ⊗ₜ[R] x) ι where
  index := ρ.index
  left i := (1 : S) ⊗ₜ[R] ρ.left i
  right i := s ⊗ₜ[R] ρ.right i
  eq := by
    rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, ← ρ.eq]
    simp [TensorProduct.tmul_sum]

variable [Module.Finite R C] [Module.Projective R C]

theorem dualCoordinateBaseChange_mul_tmul
    (s t u : S) (f g : DualCoordinate R C) (x : C) :
    (dualCoordinateBaseChangeLinearEquiv R C S (s ⊗ₜ[R] f) *
      dualCoordinateBaseChangeLinearEquiv R C S (t ⊗ₜ[R] g)) (u ⊗ₜ[R] x) =
        s * t * u * algebraMap R S ((f * g) x) := by
  rw [(scalarExtensionRepr R S C (Coalgebra.Repr.arbitrary R x) u).convMul_apply,
    (Coalgebra.Repr.arbitrary R x).convMul_apply]
  simp [scalarExtensionRepr, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

end CoalgebraBaseChange

section BialgebraBaseChange

variable (S : Type w) [CommRing S] [Algebra R S]
variable (A : Type v) [CommRing A] [Bialgebra R A] [Coalgebra.IsCocomm R A]
variable [Module.Finite R A] [Module.Projective R A]

local instance : CommRing (DualCoordinate R A) := LinearMap.convCommRing
local instance : Algebra R (DualCoordinate R A) := LinearMap.convAlgebra
local instance : CommRing (S ⊗[R] DualCoordinate R A) := Algebra.TensorProduct.instCommRing
local instance : CommRing (DualCoordinate S (S ⊗[R] A)) := LinearMap.convCommRing
local instance : Algebra S (DualCoordinate S (S ⊗[R] A)) := LinearMap.convAlgebra

theorem dualCoordinateBaseChange_mul (a b : S ⊗[R] DualCoordinate R A) :
    dualCoordinateBaseChangeLinearEquiv R A S (a * b) =
      dualCoordinateBaseChangeLinearEquiv R A S a *
        dualCoordinateBaseChangeLinearEquiv R A S b := by
  induction a using TensorProduct.inductionOn with
  | add a₁ a₂ ha₁ ha₂ => simp [add_mul, ha₁, ha₂]
  | tmul s f =>
    induction b using TensorProduct.inductionOn with
    | add b₁ b₂ hb₁ hb₂ => simp [mul_add, hb₁, hb₂]
    | tmul t g =>
      apply WithConv.ext
      apply AlgebraTensorModule.ext
      intro u x
      change dualCoordinateBaseChangeLinearEquiv R A S
        ((s ⊗ₜ[R] f) * (t ⊗ₜ[R] g)) (u ⊗ₜ[R] x) =
          (dualCoordinateBaseChangeLinearEquiv R A S (s ⊗ₜ[R] f) *
            dualCoordinateBaseChangeLinearEquiv R A S (t ⊗ₜ[R] g)) (u ⊗ₜ[R] x)
      rw [Algebra.TensorProduct.tmul_mul_tmul,
        dualCoordinateBaseChangeLinearEquiv_apply, dualCoordinateBaseChange_mul_tmul]

/-- The canonical base-change comparison preserves the coordinate algebra. -/
def dualCoordinateBaseChangeAlgEquiv :
    S ⊗[R] DualCoordinate R A ≃ₐ[S] DualCoordinate S (S ⊗[R] A) :=
  AlgEquiv.ofLinearEquiv (dualCoordinateBaseChangeLinearEquiv R A S)
    (by
      apply WithConv.ext
      apply AlgebraTensorModule.ext
      intro s x
      change dualCoordinateBaseChangeLinearEquiv R A S 1 (s ⊗ₜ[R] x) =
        (1 : DualCoordinate S (S ⊗[R] A)) (s ⊗ₜ[R] x)
      rw [Algebra.TensorProduct.one_def, dualCoordinateBaseChangeLinearEquiv_apply]
      simp [Algebra.smul_def, mul_comm])
    (dualCoordinateBaseChange_mul R S A)

end BialgebraBaseChange

section Characters

variable {C D : Type*} [AddCommGroup C] [Module R C] [Coalgebra R C]
variable [AddCommGroup D] [Module R D] [Coalgebra R D]

/-- Transport of group-like elements along an actual coalgebra isomorphism. -/
def groupLikeCongr (e : C ≃ₗc[R] D) : GroupLike R C ≃ GroupLike R D where
  toFun x := ⟨e x.val, x.isGroupLikeElem_val.map e⟩
  invFun x := ⟨e.symm x.val, x.isGroupLikeElem_val.map e.symm⟩
  left_inv x := by apply GroupLike.val_injective; exact e.symm_apply_apply x.val
  right_inv x := by apply GroupLike.val_injective; exact e.apply_symm_apply x.val

variable (S : Type w) [CommRing S] [Algebra R S]
variable (A : Type v) [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
variable [Module.Finite R A] [Module.Projective R A]

local instance : CommRing (DualCoordinate R A) := LinearMap.convCommRing
local instance : Algebra R (DualCoordinate R A) := LinearMap.convAlgebra
local instance : CommRing (DualCoordinate S (S ⊗[R] A)) := LinearMap.convCommRing
local instance : Algebra S (DualCoordinate S (S ⊗[R] A)) := LinearMap.convAlgebra

/-- For every base-change algebra S, points of the dual coordinate scheme
are the group-like units in S ⊗ A, the affine description of characters.
This uses the constructed Hopf dual and canonical scalar-extension map. -/
def affineDualPointsEquivCharacters :
    (DualCoordinate R A →ₐ[R] S) ≃ GroupLike S (S ⊗[R] A) :=
  (AlgHom.liftEquiv R S (DualCoordinate R A) S).trans <|
    ((dualCoordinateBaseChangeAlgEquiv R S A).arrowCongr (AlgEquiv.refl : S ≃ₐ[S] S)).trans <|
      (groupLikeDualEquivAlgHom S (DualCoordinate S (S ⊗[R] A))).symm.trans <|
        (groupLikeCongr S (dualCoordinateBidualBialgEquiv S (S ⊗[R] A)).toCoalgEquiv).symm

/-- The character correspondence is the canonical evaluation pairing. -/
theorem affineDualPointsEquivCharacters_symm_apply
    (z : GroupLike S (S ⊗[R] A)) (f : DualCoordinate R A) :
    (affineDualPointsEquivCharacters R S A).symm z f =
      dualCoordinateBaseChangeLinearEquiv R A S (1 ⊗ₜ[R] f) z.val := rfl

theorem affineDualPointsEquivCharacters_symm_apply_dual
    (z : GroupLike S (S ⊗[R] A)) (f : DualCoordinate R A) :
    (affineDualPointsEquivCharacters R S A).symm z f =
      Module.Dual.baseChange S f.ofConv z.val := by
  rw [affineDualPointsEquivCharacters_symm_apply]
  have h : (dualCoordinateBaseChangeLinearEquiv R A S (1 ⊗ₜ[R] f)).ofConv =
      Module.Dual.baseChange S f.ofConv := by
    apply AlgebraTensorModule.ext
    intro s x
    simp [Algebra.smul_def, mul_comm]
  exact congrArg (fun g => g z.val) h

end Characters

variable (S : Type w) [CommRing S] [Algebra R S]

/-- The scalar extensions of the original dual functionals separate points
after every base change, including nonflat base changes. -/
theorem scalarExtension_dual_ext {x y : S ⊗[R] M}
    (h : ∀ f : Module.Dual R M, f.baseChange S x = f.baseChange S y) : x = y := by
  apply (Module.evalEquiv S (S ⊗[R] M)).injective
  apply LinearMap.ext
  intro g
  obtain ⟨t, rfl⟩ := (finiteProjectiveDualBaseChangeEquiv R M S).surjective g
  change finiteProjectiveDualBaseChangeEquiv R M S t x =
    finiteProjectiveDualBaseChangeEquiv R M S t y
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simp [ha, hb]
  | tmul s f =>
    change (dualModuleBaseChangeMap R M S (s ⊗ₜ[R] f)) x =
      (dualModuleBaseChangeMap R M S (s ⊗ₜ[R] f)) y
    simp only [dualModuleBaseChangeMap, LinearMap.liftBaseChange_tmul,
      LinearMap.smul_apply, h]

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DualAlgebra.Construction
