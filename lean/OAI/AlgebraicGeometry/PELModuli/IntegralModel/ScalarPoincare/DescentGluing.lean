import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ScalarPoincare.LineDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ScalarPoincare.IsoNormalization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.MappedRelationGluing
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.SquareTransportOver
import OAI.AlgebraicGeometry.Picard.PoincareBundle.UnderlyingDescentOnOver

/-! # Descent Gluing -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual gluing of the scalar Poincare descent datum is exactly
the scalar-transported normalized isomorphism, on the prescribed relation. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left) (hrigid : U.PrescribedRigid)
    {S : Scheme.{0}} (b : S ⟶ Spec (.of R)) {Y : Over S}
    (q : (Over.pullback b).obj U.prescribedPoincareSpace ⟶ Y)
    (hq : IsKernelPair q.left ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left
      ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareLineDescentData_gluing :
    (U.scalarPoincareLineDescentData hU π hk hrigid b q hq).hom
      (((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left ≫ q.left)
      (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left
      ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left hq.w rfl =
      (U.scalarPoincareNormalizedIso hU π hk hrigid b).hom := by
  let G := Over.pullback b ⋙ Over.map b
  let q₀ := (Over.map b).map q
  let src := DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection
  let t := U.prescribedPoincareTarget π hU hk
  let v := (Scalar.Line.scalarTotalProjection b).app U.prescribedPoincareSpace
  let ρ := (Scalar.Line.scalarTotalProjection b).app (U.prescribedPoincareOverlap π)
  let F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks (Spec (.of R))
  let L := U.prescribedPoincareLine.sheaf
  let lin := U.prescribedPoincareLineLinearization hU π hk hrigid
  have hq₀ : IsKernelPair q₀ (G.map src) (G.map t) :=
    IsPullback.of_map (F := Over.forget _) (Over.OverMorphism.ext hq.w) hq
  have hs : ρ ≫ src = G.map src ≫ v := ((Scalar.Line.scalarTotalProjection b).naturality src).symm
  have ht : ρ ≫ t = G.map t ≫ v := ((Scalar.Line.scalarTotalProjection b).naturality t).symm
  let D := lin.mappedDescentData F π U.prescribedPoincareProjection t
    (U.prescribedPoincareTarget_projection π hU hk) (U.prescribedPoincareTarget_normalized hU π hk hrigid)
    (U.prescribedPoincareTarget_cocycle hU π hk hrigid) L v (G.map src) (G.map t) ρ hs ht q₀ hq₀
  have h₁ := Picard.PoincareBundle.UnderlyingDescentOnOver.hom_eq q₀
    Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks D (G.map t ≫ q₀)
      (G.map src) (G.map t) hq₀.w rfl
  have h₂ := lin.mappedDescentData_relation F π U.prescribedPoincareProjection t
    (U.prescribedPoincareTarget_projection π hU hk) (U.prescribedPoincareTarget_normalized hU π hk hrigid)
    (U.prescribedPoincareTarget_cocycle hU π hk hrigid) L v (G.map src) (G.map t) ρ hs ht q₀ hq₀
  have h₃ := LineBundle.SquareTransportOver.lineBundleSquareTransportIso_hom_eq_overPointMorphism U.prescribedPoincareLine src t v ρ
    (G.map src) (G.map t) hs.symm ht.symm (U.prescribedPoincareNormalizedIso hU π hk hrigid)
  exact h₁.trans (h₂.trans h₃.symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
