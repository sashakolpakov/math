import OAI.RepresentationTheory.Theta.Geometric.SquareZero.TensorDescent
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Zero Unit Naturality -/

namespace OAI.RepresentationTheory.Theta.Geometric.Square.ZeroUnitNaturality

noncomputable section

section

/-! The unique normalized coefficient lifts commute with restriction to
smaller affine charts and reflect the change-of-frame equations. -/

open scoped TensorProduct

theorem tensorMap_base_coefficient_commute
    {R S B C : Type*} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    [CommRing B] [Algebra ℂ B] [CommRing C] [Algebra ℂ C]
    (i : R →ₐ[ℂ] S) (f : B →ₐ[ℂ] C) (x : R ⊗[ℂ] B) :
    Algebra.TensorProduct.map i (AlgHom.id ℂ C) (Algebra.TensorProduct.map (AlgHom.id ℂ R) f x) =
      Algebra.TensorProduct.map (AlgHom.id ℂ S) f (Algebra.TensorProduct.map i (AlgHom.id ℂ B) x) := by
  have h : (Algebra.TensorProduct.map i (AlgHom.id ℂ C)).comp
      (Algebra.TensorProduct.map (AlgHom.id ℂ R) f) =
      (Algebra.TensorProduct.map (AlgHom.id ℂ S) f).comp
        (Algebra.TensorProduct.map i (AlgHom.id ℂ B)) := by
    simp only [← Algebra.TensorProduct.map_comp, AlgHom.comp_id, AlgHom.id_comp]
  exact DFunLike.congr_fun h x

variable {M R S B C : Type*} [AddCommGroup M] [Module ℂ M] [Module ℂᵐᵒᵖ M]
    [IsCentralScalar ℂ M] [CommRing R] [Algebra ℂ R] [Nontrivial R]
    [CommRing S] [Algebra ℂ S] [CommRing B] [Algebra ℂ B] [CommRing C] [Algebra ℂ C]

def squareZeroTensorUnitLift
    (i : M →ₗ[ℂ] R) (hi : Function.Injective i) (hsq : ∀ x y, i x * i y = 0)
    (q : R →ₐ[ℂ] S) (he : Function.Exact i q.toLinearMap) (x : (R ⊗[ℂ] B)ˣ)
    (hx : Algebra.TensorProduct.map q (AlgHom.id ℂ B) (x : R ⊗[ℂ] B) = 1) :
    (TrivSqZeroExt ℂ M ⊗[ℂ] B)ˣ :=
  (SquareZero.TensorDescent.squareZeroTensor_exists_unit_lift_of_reduction_one i hi hsq q he x hx).exists.choose

theorem squareZeroTensorUnitLift_spec
    (i : M →ₗ[ℂ] R) (hi : Function.Injective i) (hsq : ∀ x y, i x * i y = 0)
    (q : R →ₐ[ℂ] S) (he : Function.Exact i q.toLinearMap) (x : (R ⊗[ℂ] B)ˣ)
    (hx : Algebra.TensorProduct.map q (AlgHom.id ℂ B) (x : R ⊗[ℂ] B) = 1) :
    Algebra.TensorProduct.map (SquareZero.Subalgebra.squareZeroSubalgebraMap i hsq) (AlgHom.id ℂ B)
      (squareZeroTensorUnitLift i hi hsq q he x hx : TrivSqZeroExt ℂ M ⊗[ℂ] B) = x :=
  (SquareZero.TensorDescent.squareZeroTensor_exists_unit_lift_of_reduction_one i hi hsq q he x hx).exists.choose_spec

theorem squareZeroTensorUnitLift_natural
    (i : M →ₗ[ℂ] R) (hi : Function.Injective i) (hsq : ∀ x y, i x * i y = 0)
    (q : R →ₐ[ℂ] S) (he : Function.Exact i q.toLinearMap) (f : B →ₐ[ℂ] C)
    (x : (R ⊗[ℂ] B)ˣ) (y : (R ⊗[ℂ] C)ˣ)
    (hf : Algebra.TensorProduct.map (AlgHom.id ℂ R) f (x : R ⊗[ℂ] B) = y)
    (hx : Algebra.TensorProduct.map q (AlgHom.id ℂ B) (x : R ⊗[ℂ] B) = 1)
    (hy : Algebra.TensorProduct.map q (AlgHom.id ℂ C) (y : R ⊗[ℂ] C) = 1) :
    Algebra.TensorProduct.map (AlgHom.id ℂ (TrivSqZeroExt ℂ M)) f
      (squareZeroTensorUnitLift i hi hsq q he x hx : TrivSqZeroExt ℂ M ⊗[ℂ] B) =
      (squareZeroTensorUnitLift i hi hsq q he y hy : TrivSqZeroExt ℂ M ⊗[ℂ] C) := by
  apply SquareZero.TensorDescent.squareZeroTensorMap_injective i hi hsq
  rw [tensorMap_base_coefficient_commute, squareZeroTensorUnitLift_spec,
    squareZeroTensorUnitLift_spec, hf]

theorem squareZeroTensor_transition_reflects
    (i : M →ₗ[ℂ] R) (hi : Function.Injective i) (hsq : ∀ x y, i x * i y = 0)
    (a b u v : TrivSqZeroExt ℂ M ⊗[ℂ] B)
    (h : Algebra.TensorProduct.map (SquareZero.Subalgebra.squareZeroSubalgebraMap i hsq) (AlgHom.id ℂ B) a *
        Algebra.TensorProduct.map (SquareZero.Subalgebra.squareZeroSubalgebraMap i hsq) (AlgHom.id ℂ B) u =
      Algebra.TensorProduct.map (SquareZero.Subalgebra.squareZeroSubalgebraMap i hsq) (AlgHom.id ℂ B) v *
        Algebra.TensorProduct.map (SquareZero.Subalgebra.squareZeroSubalgebraMap i hsq) (AlgHom.id ℂ B) b) :
    a * u = v * b := by
  apply SquareZero.TensorDescent.squareZeroTensorMap_injective i hi hsq
  simpa only [map_mul] using h

end

/-! A coefficient on a complex scalar extension that agrees on its two
copies comes from the original coefficient algebra. The proof uses a
complex linear retraction of constants, not a ring-valued point. -/

open scoped TensorProduct

variable {S B : Type*} [CommRing S] [Algebra ℂ S] [Nontrivial S]
    [CommRing B] [Algebra ℂ B]

theorem tensor_constant_of_two_copies_eq (x : S ⊗[ℂ] B)
    (hx : Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : S →ₐ[ℂ] S ⊗[ℂ] S)
        (AlgHom.id ℂ B) x =
      Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight : S →ₐ[ℂ] S ⊗[ℂ] S)
        (AlgHom.id ℂ B) x) :
    ∃ b : B, Algebra.TensorProduct.includeRight b = x := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ (show (1 : S) ≠ 0 from one_ne_zero)
  let c : S ⊗[ℂ] B →ₗ[ℂ] B := (TensorProduct.lid ℂ B).toLinearMap.comp (l.rTensor B)
  let d : S ⊗[ℂ] S →ₗ[ℂ] S := (TensorProduct.lid ℂ S).toLinearMap.comp (l.rTensor S)
  have hleft (v : S ⊗[ℂ] B) : d.rTensor B
      (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : S →ₐ[ℂ] S ⊗[ℂ] S)
        (AlgHom.id ℂ B) v) = Algebra.TensorProduct.includeRight (c v) := by
    induction v using TensorProduct.inductionOn with
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul s b => simp [c, d, TensorProduct.smul_tmul]
  have hright (v : S ⊗[ℂ] B) : d.rTensor B
      (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight : S →ₐ[ℂ] S ⊗[ℂ] S)
        (AlgHom.id ℂ B) v) = v := by
    induction v using TensorProduct.inductionOn with
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul s b => simp [d, hl]
  exact ⟨c x, (hleft x).symm.trans ((congrArg (d.rTensor B) hx).trans (hright x))⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Square.ZeroUnitNaturality
