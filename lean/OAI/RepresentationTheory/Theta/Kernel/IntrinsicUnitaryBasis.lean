import OAI.RepresentationTheory.Weil.AdelicSplitting.UnitaryBase

/-! # Intrinsic Unitary Basis -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicUnitaryBasis.Intrinsic

/-! Changing an orthonormal basis conjugates the actual unitary group. -/

open scoped Classical _root_.Matrix

open OAI.RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction

variable {I R : Type} [Fintype I] [DecidableEq I] [CommRing R] [StarRing R]

theorem unitary_in_basis (H : Matrix I I R) (B : (Matrix I I R)ˣ) (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H) :
    (B⁻¹ * g.val * B).val.conjTranspose * (B.val.conjTranspose * H * B.val) *
        (B⁻¹ * g.val * B).val = B.val.conjTranspose * H * B.val := by
  have hi : B.inv.conjTranspose * B.val.conjTranspose = 1 := by
    rw [← Matrix.conjTranspose_mul,B.val_inv,Matrix.conjTranspose_one]
  change (B.inv * g.val.val * B.val).conjTranspose * (B.val.conjTranspose * H * B.val) *
    (B.inv * g.val.val * B.val) = _
  simp only [Matrix.conjTranspose_mul]
  calc
    _ = B.val.conjTranspose * g.val.val.conjTranspose *
        (B.inv.conjTranspose * B.val.conjTranspose) * H *
          (B.val * B.inv) * g.val.val * B.val := by simp only [Matrix.mul_assoc]
    _ = B.val.conjTranspose * (g.val.val.conjTranspose * H * g.val.val) * B.val := by
      rw [hi,B.val_inv]
      simp only [Matrix.mul_one,Matrix.mul_assoc]
    _ = _ := by rw [g.property]

def unitaryInBasis (H : Matrix I I R) (B : (Matrix I I R)ˣ) :
    Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H →* Weil.AdelicSplitting.UnitaryBase.Construction.Unitary (B.val.conjTranspose * H * B.val) where
  toFun g := ⟨B⁻¹ * g.val * B,unitary_in_basis H B g⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g h := by
    apply Subtype.ext
    change B⁻¹ * (g.val * h.val) * B = (B⁻¹ * g.val * B) * (B⁻¹ * h.val * B)
    group

end RepresentationTheory.Theta.Kernel.IntrinsicUnitaryBasis.Intrinsic

namespace RepresentationTheory.Theta.Kernel.IntrinsicUnitaryBasis.IntrinsicEquiv

/-! The orthonormal-coordinate unitary map is an actual group equivalence. -/

open scoped Classical _root_.Matrix

open OAI.RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction OAI.RepresentationTheory.Theta.Kernel.IntrinsicUnitaryBasis.Intrinsic

variable {I R : Type} [Fintype I] [DecidableEq I] [CommRing R] [StarRing R]

theorem twice_changed_form (H : Matrix I I R) (B : (Matrix I I R)ˣ) :
    B.inv.conjTranspose * (B.val.conjTranspose * H * B.val) * B.inv = H := by
  have hT : B.inv.conjTranspose * B.val.conjTranspose = 1 := by
    rw [← Matrix.conjTranspose_mul,B.val_inv,Matrix.conjTranspose_one]
  calc
    _ = (B.inv.conjTranspose * B.val.conjTranspose) * H * (B.val * B.inv) := by
      simp only [Matrix.mul_assoc]
    _ = H := by rw [hT,B.val_inv,Matrix.one_mul,Matrix.mul_one]

def unitaryOutOfBasis (H : Matrix I I R) (B : (Matrix I I R)ˣ)
    (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary (B.val.conjTranspose * H * B.val)) : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H :=
  ⟨B * g.val * B⁻¹,by
    have h := Intrinsic.unitary_in_basis (B.val.conjTranspose * H * B.val) B⁻¹ g
    change (B * g.val * B⁻¹).val.conjTranspose *
      (B.inv.conjTranspose * (B.val.conjTranspose * H * B.val) * B.inv) *
      (B * g.val * B⁻¹).val = B.inv.conjTranspose * (B.val.conjTranspose * H * B.val) * B.inv at h
    rwa [twice_changed_form] at h⟩

def unitaryBasisEquiv (H : Matrix I I R) (B : (Matrix I I R)ˣ) :
    Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H ≃* Weil.AdelicSplitting.UnitaryBase.Construction.Unitary (B.val.conjTranspose * H * B.val) where
  toFun := Intrinsic.unitaryInBasis H B
  invFun := unitaryOutOfBasis H B
  left_inv g := by
    apply Subtype.ext
    change B * (B⁻¹ * g.val * B) * B⁻¹ = g.val
    group
  right_inv g := by
    apply Subtype.ext
    change B⁻¹ * (B * g.val * B⁻¹) * B = g.val
    group
  map_mul' := (Intrinsic.unitaryInBasis H B).map_mul

end RepresentationTheory.Theta.Kernel.IntrinsicUnitaryBasis.IntrinsicEquiv

end

end OAI
