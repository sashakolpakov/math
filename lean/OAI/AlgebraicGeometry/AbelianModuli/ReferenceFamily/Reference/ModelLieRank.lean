import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.TangentSignature
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ModelDerivative
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Lie

/-! # Model Lie Rank -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ModelLieRank.ReferenceAlgebraicModel

noncomputable section

/-! The algebraized reference fiber has the exact PEL Lie signature
on the original dual-number points of its scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeActionEigenEquiv (τ : E →+* ℂ) : F.actionEigenSpace τ ≃ₗ[ℂ]
    Intrinsic.Lie.nativeLieEigenspace M.abelianScheme M.integralAction
      (τ.comp (algebraMap (NumberField.RingOfIntegers E) E)) where
  toFun v := ⟨M.periodDifferential v.val, by
    intro a
    change M.actionDifferential a (M.periodDifferential v.val) = τ (a : E) • M.periodDifferential v.val
    exact (M.periodDifferential_action a v.val).trans
      ((congrArg M.periodDifferential (v.property a)).trans (map_smul M.periodDifferential _ _))⟩
  invFun v := ⟨M.periodDifferential.symm v.val, by
    intro a
    apply M.periodDifferential.injective
    let w : RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian := v.val
    have hv : M.actionDifferential a w = τ (a : E) • w := v.property a
    change M.periodDifferential (F.action a (M.periodDifferential.symm w)) =
      M.periodDifferential (τ (a : E) • M.periodDifferential.symm w)
    calc
      M.periodDifferential (F.action a (M.periodDifferential.symm w)) =
          M.actionDifferential a (M.periodDifferential (M.periodDifferential.symm w)) :=
        (M.periodDifferential_action a _).symm
      _ = M.actionDifferential a w := by rw [ContinuousLinearEquiv.apply_symm_apply]
      _ = τ (a : E) • w := hv
      _ = M.periodDifferential (τ (a : E) • M.periodDifferential.symm w) := by
        rw [map_smul, ContinuousLinearEquiv.apply_symm_apply]⟩
  left_inv v := Subtype.ext (M.periodDifferential.symm_apply_apply v.val)
  right_inv v := Subtype.ext (M.periodDifferential.apply_symm_apply v.val)
  map_add' u v := Subtype.ext (map_add M.periodDifferential u.val v.val)
  map_smul' c v := Subtype.ext (map_smul M.periodDifferential c v.val)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.hasNativeLieRank (τ : E ≃ₐ[ℚ] E) :
    LieRanks.HasLieRank M.abelianScheme M.integralAction
      ((P.μ.comp τ.toRingHom).comp (algebraMap (NumberField.RingOfIntegers E) E)) (P.lieRank τ) := by
  apply LieRanks.HasLieRank.of_native_finrank
  rw [← (M.nativeActionEigenEquiv (P.μ.comp τ.toRingHom)).finrank_eq]
  exact F.actionEigenSpace_finrank hP τ

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ModelLieRank.ReferenceAlgebraicModel
