import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.Point
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.ScalarChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointScalarTransport

/-! # Scalar Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Every actual scalar-changed PEL comparison induces the prescribed
dual transport on the original arithmetic family, by rigidity. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R R' : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [CommRing R'] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q)
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPointTransport_scalar_fst (hrigid : U.PrescribedRigid)
    (φ : R →+* R') (T : Over (Spec (.of R'))) [IsReduced T.left]
    (f g : T ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X)
    (h : ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom φ))).homEquiv T X).symm f ≫ π =
      ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom φ))).homEquiv T X).symm g ≫ π)
    (e : PEL.Iso.PolarizedActionIso ((U.baseChange φ).forgetAuxiliary.pullback f).data
      ((U.baseChange φ).forgetAuxiliary.pullback g).data)
    (x : T.left ⟶ (U.baseChange φ).forgetAuxiliary.data.polarized.dual.abelian.scheme.left)
    (hx : x ≫ (U.baseChange φ).forgetAuxiliary.data.polarized.dual.abelian.scheme.hom = f.left) :
    have : IsReduced ((Over.map (Spec.map (CommRingCat.ofHom φ))).obj T).left :=
      inferInstanceAs (IsReduced T.left)
    let v := pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ))
    Family.PointBaseChange.FamilyPointTransport.transport (U.baseChange φ).forgetAuxiliary.data.polarized.dual.abelian.scheme
        f.left g.left e.polarized.dual x hx ≫
          pullback.fst U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom v =
      U.prescribedDualPointTransport hU π hk
        (((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom φ))).homEquiv T X).symm f)
        (((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom φ))).homEquiv T X).symm g) h
        (x ≫ pullback.fst U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom v)
        (by rw [Category.assoc, pullback.condition, ← Category.assoc]; exact congrArg (fun k => k ≫ v) hx) := by
  let v := pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ))
  let f₀ := ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom φ))).homEquiv T X).symm f
  let g₀ := ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom φ))).homEquiv T X).symm g
  have : IsReduced ((Over.map (Spec.map (CommRingCat.ofHom φ))).obj T).left :=
    inferInstanceAs (IsReduced T.left)
  let ef := PEL.Iso.PolarizedActionIso.pullbackComp U.forgetAuxiliary.data v f.left
  let eg := PEL.Iso.PolarizedActionIso.pullbackComp U.forgetAuxiliary.data v g.left
  let e₀ : PEL.Iso.PolarizedActionIso (U.forgetAuxiliary.pullback f₀).data
      (U.forgetAuxiliary.pullback g₀).data := ef.symm.trans (e.trans eg)
  have he : e₀ = U.prescribedTransport hU π hk f₀ g₀ h :=
    U.prescribedIso_unique hrigid f₀ g₀ e₀ _
  have hed : Family.PointScalarTransport.FamilyPointTransport.flattenedTransportIso
      U.forgetAuxiliary.data.polarized.dual.abelian.scheme v f.left g.left e.polarized.dual =
        e₀.polarized.dual := by
    apply Iso.ext
    change ((Over.pullbackComp f.left v).hom.app _ ≫ e.polarized.dual.hom ≫
        (Over.pullbackComp g.left v).inv.app _) =
      (U.forgetAuxiliary.data.polarized.dual.abelian.pullbackCompIso v f.left).hom ≫
        e.polarized.dual.hom ≫
          (U.forgetAuxiliary.data.polarized.dual.abelian.pullbackCompIso v g.left).inv
    rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_hom, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv]
    rfl
  have hp := Family.PointScalarTransport.FamilyPointTransport.transport_scalar_fst
    U.forgetAuxiliary.data.polarized.dual.abelian.scheme v f.left g.left e.polarized.dual x hx
  rw [hed, he] at hp
  exact hp

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
