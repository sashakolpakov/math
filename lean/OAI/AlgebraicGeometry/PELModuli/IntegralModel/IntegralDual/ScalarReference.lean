import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.ScalarRelation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.ReferenceDualTransport

/-! # Scalar Reference -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual scalar-changed prescribed relation is coequalized by
projection to a reference dual whenever the full PEL comparison is given. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R R' : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [CommRing R'] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarDualOverlap_reference_coequalizes (hrigid : U.PrescribedRigid) (φ : R →+* R')
    [IsReduced ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj (U.prescribedDualOverlap π)).left]
    (B : PEL.Has.PolarizedActionData E (3 * s) P.polarizationType N
      ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q).left)
    (a : PEL.Iso.PolarizedActionIso (B.pullback ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).map π).left)
      (U.baseChange φ).forgetAuxiliary.data) :
    U.scalarDualSourcePoint π φ ≫ PEL.Iso.PolarizedActionIso.referenceDualProjection B
        ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).map π).left a =
      U.scalarDualTargetPoint π φ hU hk ≫ PEL.Iso.PolarizedActionIso.referenceDualProjection B
        ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).map π).left a := by
  let F := Over.pullback (Spec.map (CommRingCat.ofHom φ))
  let f := F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection ≫ U.prescribedDualProjection)
  let g := F.map (DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection)
  have hfg : f ≫ F.map π = g ≫ F.map π := by
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map (DescentCocycleChange.DescentCocycle.source_condition π U.prescribedDualProjection)
  let e := PEL.Iso.PolarizedActionIso.referenceTransport B (F.map π).left a f.left g.left
    (congrArg Over.Hom.left hfg)
  have ht := U.scalarDualRelation_transport hU π hk hrigid φ e
  have hp := PEL.Iso.PolarizedActionIso.referenceTransport_dual_point B (F.map π).left a f.left g.left
    (congrArg Over.Hom.left hfg) (U.scalarDualSourcePoint π φ) (U.scalarDualSourcePoint_base π φ)
  exact hp.symm.trans (congrArg (fun k => k ≫
    PEL.Iso.PolarizedActionIso.referenceDualProjection B (F.map π).left a) ht)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
