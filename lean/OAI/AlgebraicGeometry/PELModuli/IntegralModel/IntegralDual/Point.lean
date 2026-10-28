import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.Transport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointBaseChange

/-! # Point -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

section

/-! The canonical prescribed PEL comparisons act on actual dual scheme
points, naturally in every reduced test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q T W : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q)
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedTransport_baseChange_dual (hrigid : U.PrescribedRigid)
    [IsReduced T.left] [IsReduced W.left] (f g : T ⟶ X)
    (h : f ≫ π = g ≫ π) (k : W ⟶ T) :
    Family.PointBaseChange.FamilyPointTransport.baseChangeIso U.forgetAuxiliary.data.polarized.dual.abelian.scheme
      f.left g.left k.left (U.prescribedTransport hU π hk f g h).polarized.dual =
      (U.prescribedTransport hU π hk (k ≫ f) (k ≫ g)
        (by simpa only [Category.assoc] using congrArg (fun a => k ≫ a) h)).polarized.dual := by
  have H := congrArg (fun e => e.polarized.dual.hom)
    (U.prescribedTransport_pullback hU π hk hrigid f g h k)
  change (U.forgetAuxiliary.data.polarized.dual.abelian.pullbackCompIso f.left k.left).hom ≫
    (Over.pullback k.left).map (U.prescribedTransport hU π hk f g h).polarized.dual.hom ≫
    (U.forgetAuxiliary.data.polarized.dual.abelian.pullbackCompIso g.left k.left).inv = _ at H
  rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_hom, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv] at H
  exact Iso.ext H

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPointTransport [IsReduced T.left] (f g : T ⟶ X)
    (h : f ≫ π = g ≫ π) (x : T.left ⟶ U.forgetAuxiliary.data.polarized.dual.abelian.scheme.left)
    (hx : x ≫ U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom = f.left) :
    T.left ⟶ U.forgetAuxiliary.data.polarized.dual.abelian.scheme.left :=
  Family.PointBaseChange.FamilyPointTransport.transport U.forgetAuxiliary.data.polarized.dual.abelian.scheme f.left g.left
    (U.prescribedTransport hU π hk f g h).polarized.dual x hx

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPointTransport_base [IsReduced T.left] (f g : T ⟶ X)
    (h : f ≫ π = g ≫ π) (x : T.left ⟶ U.forgetAuxiliary.data.polarized.dual.abelian.scheme.left)
    (hx : x ≫ U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom = f.left) :
    U.prescribedDualPointTransport hU π hk f g h x hx ≫
      U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom = g.left :=
  Family.PointBaseChange.FamilyPointTransport.transport_base _ _ _ _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPointTransport_self (hrigid : U.PrescribedRigid) [IsReduced T.left]
    (f : T ⟶ X) (x : T.left ⟶ U.forgetAuxiliary.data.polarized.dual.abelian.scheme.left)
    (hx : x ≫ U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom = f.left) :
    U.prescribedDualPointTransport hU π hk f f rfl x hx = x := by
  unfold IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPointTransport
  rw [U.prescribedTransport_self hU π hk hrigid f]
  exact Family.PointBaseChange.FamilyPointTransport.transport_refl _ _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPointTransport_natural (hrigid : U.PrescribedRigid)
    [IsReduced T.left] [IsReduced W.left] (f g : T ⟶ X)
    (h : f ≫ π = g ≫ π) (x : T.left ⟶ U.forgetAuxiliary.data.polarized.dual.abelian.scheme.left)
    (hx : x ≫ U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom = f.left) (k : W ⟶ T) :
    U.prescribedDualPointTransport hU π hk (k ≫ f) (k ≫ g)
      (by simpa only [Category.assoc] using congrArg (fun a => k ≫ a) h)
      (k.left ≫ x) (by change (k.left ≫ x) ≫ _ = k.left ≫ f.left; rw [Category.assoc, hx]) =
      k.left ≫ U.prescribedDualPointTransport hU π hk f g h x hx := by
  unfold IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPointTransport
  rw [← U.prescribedTransport_baseChange_dual hU π hk hrigid f g h k]
  exact Family.PointBaseChange.FamilyPointTransport.transport_baseChange _ _ _ _ _ _ _

end

section

/-! Identity and composition of prescribed family transport on actual
scheme points. These follow from the proved rigid PEL comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q T : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q)
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPointTransport_of_eq (hrigid : U.PrescribedRigid) [IsReduced T.left]
    (f g : T ⟶ X) (h : f ≫ π = g ≫ π) (hfg : f = g)
    (x : T.left ⟶ U.forgetAuxiliary.data.polarized.dual.abelian.scheme.left)
    (hx : x ≫ U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom = f.left) :
    U.prescribedDualPointTransport hU π hk f g h x hx = x := by
  subst g
  exact U.prescribedDualPointTransport_self hU π hk hrigid f x hx

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPointTransport_trans (hrigid : U.PrescribedRigid) [IsReduced T.left]
    (f g j : T ⟶ X) (hfg : f ≫ π = g ≫ π) (hgj : g ≫ π = j ≫ π)
    (x : T.left ⟶ U.forgetAuxiliary.data.polarized.dual.abelian.scheme.left)
    (hx : x ≫ U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom = f.left) :
    U.prescribedDualPointTransport hU π hk g j hgj
      (U.prescribedDualPointTransport hU π hk f g hfg x hx)
      (U.prescribedDualPointTransport_base hU π hk f g hfg x hx) =
        U.prescribedDualPointTransport hU π hk f j (hfg.trans hgj) x hx := by
  have he : (U.prescribedTransport hU π hk f g hfg).polarized.dual ≪≫
      (U.prescribedTransport hU π hk g j hgj).polarized.dual =
      (U.prescribedTransport hU π hk f j (hfg.trans hgj)).polarized.dual :=
    congrArg (fun e => e.polarized.dual) (U.prescribedTransport_trans hU π hk hrigid f g j hfg hgj)
  exact (Family.PointBaseChange.FamilyPointTransport.transport_trans _ _ _ _ _ _ _).trans
    (congrArg (fun e => Family.PointBaseChange.FamilyPointTransport.transport
      U.forgetAuxiliary.data.polarized.dual.abelian.scheme f.left j.left e x hx) he)

end

/-! Explicit equation adapters for composing actual prescribed dual-family
point transports on geometric overlap diagrams. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q T : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q)
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPointTransport_congr [IsReduced T.left]
    (f g f' g' : T ⟶ X) (h : f ≫ π = g ≫ π) (h' : f' ≫ π = g' ≫ π)
    (hf : f = f') (hg : g = g')
    (x y : T.left ⟶ U.forgetAuxiliary.data.polarized.dual.abelian.scheme.left)
    (hx : x ≫ U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom = f.left)
    (hy : y ≫ U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom = f'.left) (he : x = y) :
    U.prescribedDualPointTransport hU π hk f g h x hx =
      U.prescribedDualPointTransport hU π hk f' g' h' y hy := by
  subst f'
  subst g'
  subst y
  rfl

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPointTransport_chain (hrigid : U.PrescribedRigid) [IsReduced T.left]
    (f g f' j : T ⟶ X) (hfg : f ≫ π = g ≫ π) (hfj : f' ≫ π = j ≫ π)
    (hgf : g = f') (hfj' : f ≫ π = j ≫ π)
    (x y : T.left ⟶ U.forgetAuxiliary.data.polarized.dual.abelian.scheme.left)
    (hx : x ≫ U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom = f.left)
    (hy : y ≫ U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom = f'.left)
    (he : U.prescribedDualPointTransport hU π hk f g hfg x hx = y) :
    U.prescribedDualPointTransport hU π hk f j hfj' x hx =
      U.prescribedDualPointTransport hU π hk f' j hfj y hy := by
  subst f'
  subst y
  exact (U.prescribedDualPointTransport_trans hU π hk hrigid f g j hfg hfj x hx).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
