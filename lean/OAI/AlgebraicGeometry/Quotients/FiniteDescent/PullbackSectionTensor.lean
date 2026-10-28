import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionRestrict
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Pullback Section Tensor -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionTensor

noncomputable section

/-! Tensor extension of the canonical pullback map on local sections. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

universe u

namespace Construction.PullbackSectionCoefficients

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)

def tensorMap (U : X.Opens) :
    (ModuleCat.extendScalars (f.app U).hom).obj (M.val.obj (op U)) ⟶
      ((Scheme.Modules.pullback f).obj M).val.obj (op (f ⁻¹ᵁ U)) :=
  ((ModuleCat.extendRestrictScalarsAdj (f.app U).hom).homEquiv _ _).symm
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op U))

theorem tensorMap_one_tmul (U : X.Opens) (s : Γ(M, U)) :
    tensorMap f M U ((1 : Γ(Y, f ⁻¹ᵁ U)) ⊗ₜ[Γ(X, U),(f.app U).hom] s) = PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U s := by
  have h := ((ModuleCat.extendRestrictScalarsAdj (f.app U).hom).homEquiv _ _).apply_symm_apply
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op U))
  exact ConcreteCategory.congr_hom h s

theorem tensorMap_tmul (U : X.Opens) (r : Γ(Y, f ⁻¹ᵁ U)) (s : Γ(M, U)) :
    tensorMap f M U (r ⊗ₜ[Γ(X, U),(f.app U).hom] s) = r • PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U s := by
  have h : (r ⊗ₜ[Γ(X, U),(f.app U).hom] s) =
      r • ((1 : Γ(Y, f ⁻¹ᵁ U)) ⊗ₜ[Γ(X, U),(f.app U).hom] s) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  rw [h, map_smul, tensorMap_one_tmul]

end Construction.PullbackSectionCoefficients

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionTensor
