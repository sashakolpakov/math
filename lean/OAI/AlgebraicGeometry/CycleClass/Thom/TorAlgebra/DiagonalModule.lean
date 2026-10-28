import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalTensorResolution

/-! # Diagonal Module -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DiagonalModule

noncomputable section

/-! The diagonal is the actual module obtained from multiplication
on the tensor algebra. Restriction to the right factor gives the free
rank-one module, and tensoring along that factor gives the chosen module
with its original left action. -/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalTensorProjectives OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RightRestrictionProjectives

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]

def diagonalModule : ModuleCat.{u} (R ⊗[k] R) :=
  (ModuleCat.restrictScalars (Algebra.TensorProduct.lmul' k (S := R)).toRingHom).obj
    (ModuleCat.of R R)

def rightDiagonalEquiv : (RightRestrictionProjectives.rightRestriction k R R).obj (diagonalModule k R) ≃ₗ[R] R where
  __ := AddEquiv.refl R
  map_smul' r x := by
    change Algebra.TensorProduct.lmul' k (1 ⊗ₜ[k] r) * (show R from x) = r * (show R from x)
    rw [Algebra.TensorProduct.lmul'_apply_tmul, one_mul]

instance rightDiagonal_projective : Projective ((RightRestrictionProjectives.rightRestriction k R R).obj (diagonalModule k R)) := by
  let : Module.Projective R ((RightRestrictionProjectives.rightRestriction k R R).obj (diagonalModule k R)) :=
    Module.Projective.of_equiv' (rightDiagonalEquiv k R).symm
  infer_instance

variable (N : ModuleCat.{u} R)

def diagonalTensorAddEquiv : (ExternalTensorProjectives.externalTensor k R R N).obj (diagonalModule k R) ≃+ N :=
  ((TensorProduct.congr (rightDiagonalEquiv k R) (LinearEquiv.refl R N)).trans
    (TensorProduct.lid R N)).toAddEquiv

theorem diagonalTensor_smul (r : R) (t : (ExternalTensorProjectives.externalTensor k R R N).obj (diagonalModule k R)) :
    diagonalTensorAddEquiv k R N (r • t) = r • diagonalTensorAddEquiv k R N t := by
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul x n =>
    change (Algebra.TensorProduct.lmul' k (r ⊗ₜ[k] 1) * (show R from x)) • n =
      r • ((show R from x) • n)
    rw [Algebra.TensorProduct.lmul'_apply_tmul, mul_one, mul_smul]

def diagonalTensorEquiv : (ExternalTensorProjectives.externalTensor k R R N).obj (diagonalModule k R) ≃ₗ[R] N where
  __ := diagonalTensorAddEquiv k R N
  map_smul' := diagonalTensor_smul k R N

def diagonalTensorIso : (ExternalTensorProjectives.externalTensor k R R N).obj (diagonalModule k R) ≅ N :=
  (diagonalTensorEquiv k R N).toModuleIso

def tensorResolution (P : ProjectiveResolution (diagonalModule k R)) :
    ProjectiveResolution ((ExternalTensorProjectives.externalTensor k R R N).obj (diagonalModule k R)) :=
  ExternalTensorResolution.resolution k R R N (diagonalModule k R) P

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DiagonalModule
