/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/EllipticCurve/PullbackTensorSection.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSections

/-! # Tensor Section Bilinear -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSectionBilinear

noncomputable section

/-! Bilinearity of actual tensor sections over the ring of an arbitrary open. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
universe u
local instance tensorSectionBilinearMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

theorem tensorSection_smul_left {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (r : Γ(X, U)) (x : Γ(M, U)) (y : Γ(N, U)) :
    TensorSections.tensorSection M N U (r • x) y = r • TensorSections.tensorSection M N U x y := by
  let S := X.sheaf.obj.obj (op U)
  let MM : ModuleCat S := by
    change ModuleCat ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U))
    exact M.val.obj (op U)
  let NN : ModuleCat S := by
    change ModuleCat ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U))
    exact N.val.obj (op U)
  let T : ModuleCat S := by
    change ModuleCat ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U))
    exact (M.val ⊗ N.val).obj (op U)
  let V : ModuleCat S := by
    change ModuleCat ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U))
    exact (M ⊗ N).val.obj (op U)
  let F : T →ₗ[S] V := ((TensorSections.monoidalTensorObjIso M N).inv.val.app (op U)).hom.comp
    (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (M.val ⊗ N.val)).app (op U)).hom
  let rr : S := r
  let xx : MM := x
  let yy : NN := y
  change F ((rr • xx) ⊗ₜ[S] yy) = rr • F (xx ⊗ₜ[S] yy)
  rw [← TensorProduct.smul_tmul', F.map_smul]

theorem tensorSection_smul_right {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (r : Γ(X, U)) (x : Γ(M, U)) (y : Γ(N, U)) :
    TensorSections.tensorSection M N U x (r • y) = r • TensorSections.tensorSection M N U x y := by
  rw [← TensorSections.tensorSection_smul, tensorSection_smul_left]

theorem tensorSection_smul_both {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (r s : Γ(X, U)) (x : Γ(M, U)) (y : Γ(N, U)) :
    TensorSections.tensorSection M N U (r • x) (s • y) = (r * s) • TensorSections.tensorSection M N U x y := by
  rw [tensorSection_smul_left, tensorSection_smul_right, mul_smul]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSectionBilinear
