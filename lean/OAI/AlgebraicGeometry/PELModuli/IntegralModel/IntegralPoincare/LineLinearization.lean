import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.LineCocycle
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.LineIdentity
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CocycleLinearizationDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.OverPullHom

/-! # Line Linearization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual Poincare bundle carries a fully proved ordinary
linearization on the prescribed integral relation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left) (hrigid : U.PrescribedRigid)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareLineLinearization :
    CocycleLinearizationSelf.CocycleLinearization (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks (Spec (.of R)))
      π U.prescribedPoincareProjection (U.prescribedPoincareTarget π hU hk)
      (U.prescribedPoincareTarget_projection π hU hk)
      (U.prescribedPoincareTarget_normalized hU π hk hrigid)
      (U.prescribedPoincareTarget_cocycle hU π hk hrigid) U.prescribedPoincareLine.sheaf where
  iso := U.prescribedPoincareNormalizedIso hU π hk hrigid
  identity := by
    have h := LineBundle.OverPullHom.lineBundleRestrictIso_hom_eq_overPullHom U.prescribedPoincareLine
      (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection) (U.prescribedPoincareTarget π hU hk)
      (DescentCocycleChange.DescentCocycle.diagonal π U.prescribedPoincareProjection) (𝟙 _) (𝟙 _)
      (DescentCocycleChange.DescentCocycle.diagonal_source π U.prescribedPoincareProjection)
      (U.prescribedPoincareTarget_normalized hU π hk hrigid)
      (U.prescribedPoincareNormalizedIso hU π hk hrigid)
    exact h.symm.trans (congrArg CategoryTheory.Iso.hom
      (U.prescribedPoincareNormalizedIso_identity hU π hk hrigid))
  cocycle := by
    let src := DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection
    let t := U.prescribedPoincareTarget π hU hk
    let c := DescentCocycleChange.DescentCocycle.composition π U.prescribedPoincareProjection t
      (U.prescribedPoincareTarget_projection π hU hk)
    let k₁ := Limits.pullback.fst t src
    let k₂ := Limits.pullback.snd t src
    let e := U.prescribedPoincareNormalizedIso hU π hk hrigid
    have h₁ := LineBundle.OverPullHom.lineBundleRestrictIso_hom_eq_overPullHom U.prescribedPoincareLine src t k₁
      (k₁ ≫ src) (k₂ ≫ src) rfl Limits.pullback.condition e
    have h₂ := LineBundle.OverPullHom.lineBundleRestrictIso_hom_eq_overPullHom U.prescribedPoincareLine src t k₂
      (k₂ ≫ src) (k₂ ≫ t) rfl rfl e
    have h₃ := LineBundle.OverPullHom.lineBundleRestrictIso_hom_eq_overPullHom U.prescribedPoincareLine src t c
      (k₁ ≫ src) (k₂ ≫ t)
      (DescentCocycleChange.DescentCocycle.composition_source π U.prescribedPoincareProjection t
        (U.prescribedPoincareTarget_projection π hU hk))
      (U.prescribedPoincareTarget_cocycle hU π hk hrigid) e
    exact (congrArg₂ (fun f g => f ≫ g) h₁ h₂).symm.trans
      ((congrArg CategoryTheory.Iso.hom (U.prescribedPoincareNormalizedIso_cocycle hU π hk hrigid)).trans h₃)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
