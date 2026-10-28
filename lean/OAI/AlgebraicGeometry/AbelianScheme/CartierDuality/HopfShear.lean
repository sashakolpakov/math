import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.NormCharactersEq
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.HopfAlgebra.GroupLike
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Hopf Shear -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.HopfShear.Construction.NormCharacters

noncomputable section

/-!
# CartierDuality: the universal translation and the finite-free character exponent

The coordinate automorphism of (x,y) ↦ (x,xy) preserves the first factor.
Taking the norm of a group-like unit in the second factor proves its rank
power is one. This calculation works over arbitrary commutative rings.
-/

open scoped TensorProduct

/-- Postcomposition preserves convolution, hence also convolution inverses. -/
def convPostcomp {R A C D : Type*} [CommRing R] [CommRing A] [CommRing C] [CommRing D]
    [HopfAlgebra R A] [Bialgebra R C] [Bialgebra R D] (h : C →ₐ[R] D) :
    WithConv (A →ₐ[R] C) →* WithConv (A →ₐ[R] D) where
  toFun f := WithConv.toConv (h.comp f.ofConv)
  map_one' := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro a
    exact h.commutes (Coalgebra.counit a)
  map_mul' f g := congrArg WithConv.toConv (AlgHom.comp_convMul_distrib h f g)

variable (R A : Type*) [CommRing R] [CommRing A] [HopfAlgebra R A]

/-- The first universal point in convolution notation. -/
def leftPoint : WithConv (A →ₐ[R] A ⊗[R] A) := WithConv.toConv Algebra.TensorProduct.includeLeft

/-- The second universal point in convolution notation. -/
def rightPoint : WithConv (A →ₐ[R] A ⊗[R] A) := WithConv.toConv Algebra.TensorProduct.includeRight

/-- Pullback by the universal translation (x,y) ↦ (x,xy). -/
def shearHom : (A ⊗[R] A) →ₐ[R] A ⊗[R] A :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft
    (leftPoint R A * rightPoint R A).ofConv (fun _ _ => Commute.all _ _)

/-- Pullback by the inverse universal translation (x,y) ↦ (x,x⁻¹y). -/
def unshearHom : (A ⊗[R] A) →ₐ[R] A ⊗[R] A :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft
    ((leftPoint R A)⁻¹ * rightPoint R A).ofConv (fun _ _ => Commute.all _ _)

theorem shear_left : (shearHom R A).comp Algebra.TensorProduct.includeLeft =
    Algebra.TensorProduct.includeLeft := Algebra.TensorProduct.lift_comp_includeLeft _ _ _

theorem unshear_left : (unshearHom R A).comp Algebra.TensorProduct.includeLeft =
    Algebra.TensorProduct.includeLeft := Algebra.TensorProduct.lift_comp_includeLeft _ _ _

theorem shear_post_left : convPostcomp (shearHom R A) (leftPoint R A) = leftPoint R A :=
  congrArg WithConv.toConv (shear_left R A)

theorem unshear_post_left : convPostcomp (unshearHom R A) (leftPoint R A) = leftPoint R A :=
  congrArg WithConv.toConv (unshear_left R A)

theorem shear_post_right : convPostcomp (shearHom R A) (rightPoint R A) =
    leftPoint R A * rightPoint R A :=
  congrArg WithConv.toConv (Algebra.TensorProduct.lift_comp_includeRight' _ _ _)

theorem unshear_post_right : convPostcomp (unshearHom R A) (rightPoint R A) =
    (leftPoint R A)⁻¹ * rightPoint R A :=
  congrArg WithConv.toConv (Algebra.TensorProduct.lift_comp_includeRight' _ _ _)

theorem shear_unshear : (shearHom R A).comp (unshearHom R A) = AlgHom.id R (A ⊗[R] A) := by
  apply Algebra.TensorProduct.ext
  · rw [AlgHom.comp_assoc, unshear_left, shear_left, AlgHom.id_comp]
  · apply WithConv.toConv_injective
    change convPostcomp (shearHom R A) (convPostcomp (unshearHom R A) (rightPoint R A)) = rightPoint R A
    rw [unshear_post_right, map_mul, map_inv, shear_post_left, shear_post_right, inv_mul_cancel_left]

theorem unshear_shear : (unshearHom R A).comp (shearHom R A) = AlgHom.id R (A ⊗[R] A) := by
  apply Algebra.TensorProduct.ext
  · rw [AlgHom.comp_assoc, shear_left, unshear_left, AlgHom.id_comp]
  · apply WithConv.toConv_injective
    change convPostcomp (unshearHom R A) (convPostcomp (shearHom R A) (rightPoint R A)) = rightPoint R A
    rw [shear_post_right, map_mul, unshear_post_left, unshear_post_right, mul_inv_cancel_left]

/-- The translation is an algebra isomorphism over the original base. -/
def shearBaseEquiv : (A ⊗[R] A) ≃ₐ[R] A ⊗[R] A :=
  AlgEquiv.ofAlgHom (shearHom R A) (unshearHom R A) (shear_unshear R A) (unshear_shear R A)

/-- The translation fixes the first coordinate and is an algebra
isomorphism over the coordinate algebra of that factor. -/
def shearEquiv : (A ⊗[R] A) ≃ₐ[A] A ⊗[R] A where
  toRingEquiv := (shearBaseEquiv R A).toRingEquiv
  commutes' a := AlgHom.congr_fun (shear_left R A) a

/-- The universal translation scales a group-like function in the second
factor by its value in the first factor. -/
theorem shear_groupLike (x : GroupLike R A) :
    shearEquiv R A (Algebra.TensorProduct.includeRight (R := R) (A := A) x.val) =
      algebraMap A (A ⊗[R] A) x.val * Algebra.TensorProduct.includeRight x.val := by
  have h := congrArg WithConv.ofConv (shear_post_right R A)
  have hx := AlgHom.congr_fun h x.val
  change shearHom R A (Algebra.TensorProduct.includeRight x.val) =
    (leftPoint R A * rightPoint R A) x.val at hx
  rw [AlgHom.convMul_apply, x.2.comul_eq_tmul_self, Algebra.TensorProduct.lift_tmul] at hx
  exact hx

/-- Every group-like element of a finite free commutative Hopf algebra
is killed by the rank, over any commutative base ring. -/
theorem groupLike_pow_card {ι : Type*} [Fintype ι] (b : Module.Basis ι R A) (x : GroupLike R A) :
    x ^ Fintype.card ι = 1 := by
  apply GroupLike.val_injective
  have hx : IsUnit (Algebra.TensorProduct.includeRight (R := R) (A := A) x.val) :=
    x.2.isUnit.map (Algebra.TensorProduct.includeRight (R := R) (A := A))
  exact NormCharactersEq.Construction.NormCharacters.scalar_pow_card_eq_one (b.baseChange A) (shearEquiv R A) x.val
    (Algebra.TensorProduct.includeRight x.val) hx (shear_groupLike R A x)

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.HopfShear.Construction.NormCharacters
