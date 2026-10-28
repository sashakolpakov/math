import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.Transport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointBaseChange

/-! # Point Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The canonical prescribed PEL comparisons act on actual scheme
points, naturally in every reduced test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q T W : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q)
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedTransport_baseChange_abelian (hrigid : U.PrescribedRigid)
    [IsReduced T.left] [IsReduced W.left] (f g : T ⟶ X)
    (h : f ≫ π = g ≫ π) (k : W ⟶ T) :
    Family.PointBaseChange.FamilyPointTransport.baseChangeIso U.forgetAuxiliary.data.polarized.abelian.scheme
      f.left g.left k.left (U.prescribedTransport hU π hk f g h).polarized.abelian =
      (U.prescribedTransport hU π hk (k ≫ f) (k ≫ g)
        (by simpa only [Category.assoc] using congrArg (fun a => k ≫ a) h)).polarized.abelian := by
  have H := congrArg (fun e => e.polarized.abelian.hom)
    (U.prescribedTransport_pullback hU π hk hrigid f g h k)
  change (U.forgetAuxiliary.data.polarized.abelian.pullbackCompIso f.left k.left).hom ≫
    (Over.pullback k.left).map (U.prescribedTransport hU π hk f g h).polarized.abelian.hom ≫
    (U.forgetAuxiliary.data.polarized.abelian.pullbackCompIso g.left k.left).inv = _ at H
  rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_hom, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv] at H
  exact Iso.ext H

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPointTransport [IsReduced T.left] (f g : T ⟶ X)
    (h : f ≫ π = g ≫ π) (x : T.left ⟶ U.forgetAuxiliary.data.polarized.abelian.scheme.left)
    (hx : x ≫ U.forgetAuxiliary.data.polarized.abelian.scheme.hom = f.left) :
    T.left ⟶ U.forgetAuxiliary.data.polarized.abelian.scheme.left :=
  Family.PointBaseChange.FamilyPointTransport.transport U.forgetAuxiliary.data.polarized.abelian.scheme f.left g.left
    (U.prescribedTransport hU π hk f g h).polarized.abelian x hx

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPointTransport_base [IsReduced T.left] (f g : T ⟶ X)
    (h : f ≫ π = g ≫ π) (x : T.left ⟶ U.forgetAuxiliary.data.polarized.abelian.scheme.left)
    (hx : x ≫ U.forgetAuxiliary.data.polarized.abelian.scheme.hom = f.left) :
    U.prescribedPointTransport hU π hk f g h x hx ≫
      U.forgetAuxiliary.data.polarized.abelian.scheme.hom = g.left :=
  Family.PointBaseChange.FamilyPointTransport.transport_base _ _ _ _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPointTransport_self (hrigid : U.PrescribedRigid) [IsReduced T.left]
    (f : T ⟶ X) (x : T.left ⟶ U.forgetAuxiliary.data.polarized.abelian.scheme.left)
    (hx : x ≫ U.forgetAuxiliary.data.polarized.abelian.scheme.hom = f.left) :
    U.prescribedPointTransport hU π hk f f rfl x hx = x := by
  unfold IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPointTransport
  rw [U.prescribedTransport_self hU π hk hrigid f]
  exact Family.PointBaseChange.FamilyPointTransport.transport_refl _ _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPointTransport_natural (hrigid : U.PrescribedRigid)
    [IsReduced T.left] [IsReduced W.left] (f g : T ⟶ X)
    (h : f ≫ π = g ≫ π) (x : T.left ⟶ U.forgetAuxiliary.data.polarized.abelian.scheme.left)
    (hx : x ≫ U.forgetAuxiliary.data.polarized.abelian.scheme.hom = f.left) (k : W ⟶ T) :
    U.prescribedPointTransport hU π hk (k ≫ f) (k ≫ g)
      (by simpa only [Category.assoc] using congrArg (fun a => k ≫ a) h)
      (k.left ≫ x) (by change (k.left ≫ x) ≫ _ = k.left ≫ f.left; rw [Category.assoc, hx]) =
      k.left ≫ U.prescribedPointTransport hU π hk f g h x hx := by
  unfold IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPointTransport
  rw [← U.prescribedTransport_baseChange_abelian hU π hk hrigid f g h k]
  exact Family.PointBaseChange.FamilyPointTransport.transport_baseChange _ _ _ _ _ _ _

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
