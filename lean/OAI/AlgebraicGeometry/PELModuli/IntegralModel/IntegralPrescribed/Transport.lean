import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.QuotientFibers
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.IsoRigidity

/-! # Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The quotient's equal fibers carry unique actual prescribed PEL
comparisons. Rigidity proves normalization, composition, and pullback
compatibility for these comparisons, supplying genuine descent data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q T W : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q)
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

omit [NeZero L] [IsReduced X.left] in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedIso_unique (hrigid : U.PrescribedRigid) [IsReduced T.left]
    (f g : T ⟶ X)
    (a b : PEL.Iso.PolarizedActionIso (U.forgetAuxiliary.pullback f).data
      (U.forgetAuxiliary.pullback g).data) : a = b := by
  have h := Polarized.IsoRigidity.polarizedIso_eq_of_source_rigidity (hrigid T f) a.polarized b.polarized
  cases a
  cases b
  cases h
  rfl

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedTransport [IsReduced T.left] (f g : T ⟶ X) (h : f ≫ π = g ≫ π) :
    PEL.Iso.PolarizedActionIso (U.forgetAuxiliary.pullback f).data
      (U.forgetAuxiliary.pullback g).data :=
  Classical.choice ((IntegralAuxiliary.QuotientFibers.IntegralAuxiliaryAction.quotient_eq_iff_prescribed_iso U hU π hk f g).mp h)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedTransport_self (hrigid : U.PrescribedRigid) [IsReduced T.left] (f : T ⟶ X) :
    U.prescribedTransport hU π hk f f rfl = PEL.Iso.PolarizedActionIso.refl (U.forgetAuxiliary.pullback f).data :=
  U.prescribedIso_unique hrigid f f _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedTransport_trans (hrigid : U.PrescribedRigid) [IsReduced T.left]
    (f g j : T ⟶ X) (hfg : f ≫ π = g ≫ π) (hgj : g ≫ π = j ≫ π) :
    (U.prescribedTransport hU π hk f g hfg).trans (U.prescribedTransport hU π hk g j hgj) =
      U.prescribedTransport hU π hk f j (hfg.trans hgj) :=
  U.prescribedIso_unique hrigid f j _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedTransport_pullback (hrigid : U.PrescribedRigid)
    [IsReduced T.left] [IsReduced W.left]
    (f g : T ⟶ X) (h : f ≫ π = g ≫ π) (k : W ⟶ T) :
    ((PEL.Iso.PolarizedActionIso.pullbackComp U.forgetAuxiliary.data f.left k.left).symm.trans
      ((U.prescribedTransport hU π hk f g h).pullback k.left)).trans
        (PEL.Iso.PolarizedActionIso.pullbackComp U.forgetAuxiliary.data g.left k.left) =
      U.prescribedTransport hU π hk (k ≫ f) (k ≫ g)
        (by simpa only [Category.assoc] using congrArg (fun a => k ≫ a) h) :=
  U.prescribedIso_unique hrigid (k ≫ f) (k ≫ g) _ _

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
