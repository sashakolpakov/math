import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.PointTransport

/-! # Point Equations -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

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

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPointTransport_of_eq (hrigid : U.PrescribedRigid) [IsReduced T.left]
    (f g : T ⟶ X) (h : f ≫ π = g ≫ π) (hfg : f = g)
    (x : T.left ⟶ U.forgetAuxiliary.data.polarized.abelian.scheme.left)
    (hx : x ≫ U.forgetAuxiliary.data.polarized.abelian.scheme.hom = f.left) :
    U.prescribedPointTransport hU π hk f g h x hx = x := by
  subst g
  exact U.prescribedPointTransport_self hU π hk hrigid f x hx

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPointTransport_trans (hrigid : U.PrescribedRigid) [IsReduced T.left]
    (f g j : T ⟶ X) (hfg : f ≫ π = g ≫ π) (hgj : g ≫ π = j ≫ π)
    (x : T.left ⟶ U.forgetAuxiliary.data.polarized.abelian.scheme.left)
    (hx : x ≫ U.forgetAuxiliary.data.polarized.abelian.scheme.hom = f.left) :
    U.prescribedPointTransport hU π hk g j hgj
      (U.prescribedPointTransport hU π hk f g hfg x hx)
      (U.prescribedPointTransport_base hU π hk f g hfg x hx) =
        U.prescribedPointTransport hU π hk f j (hfg.trans hgj) x hx := by
  have he : (U.prescribedTransport hU π hk f g hfg).polarized.abelian ≪≫
      (U.prescribedTransport hU π hk g j hgj).polarized.abelian =
      (U.prescribedTransport hU π hk f j (hfg.trans hgj)).polarized.abelian :=
    congrArg (fun e => e.polarized.abelian) (U.prescribedTransport_trans hU π hk hrigid f g j hfg hgj)
  exact (Family.PointBaseChange.FamilyPointTransport.transport_trans _ _ _ _ _ _ _).trans
    (congrArg (fun e => Family.PointBaseChange.FamilyPointTransport.transport
      U.forgetAuxiliary.data.polarized.abelian.scheme f.left j.left e x hx) he)

end

/-! Explicit equation adapters for composing actual prescribed-family
point transports on geometric overlap diagrams. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q T : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q)
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPointTransport_congr [IsReduced T.left]
    (f g f' g' : T ⟶ X) (h : f ≫ π = g ≫ π) (h' : f' ≫ π = g' ≫ π)
    (hf : f = f') (hg : g = g')
    (x y : T.left ⟶ U.forgetAuxiliary.data.polarized.abelian.scheme.left)
    (hx : x ≫ U.forgetAuxiliary.data.polarized.abelian.scheme.hom = f.left)
    (hy : y ≫ U.forgetAuxiliary.data.polarized.abelian.scheme.hom = f'.left) (he : x = y) :
    U.prescribedPointTransport hU π hk f g h x hx =
      U.prescribedPointTransport hU π hk f' g' h' y hy := by
  subst f'
  subst g'
  subst y
  rfl

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPointTransport_chain (hrigid : U.PrescribedRigid) [IsReduced T.left]
    (f g f' j : T ⟶ X) (hfg : f ≫ π = g ≫ π) (hfj : f' ≫ π = j ≫ π)
    (hgf : g = f') (hfj' : f ≫ π = j ≫ π)
    (x y : T.left ⟶ U.forgetAuxiliary.data.polarized.abelian.scheme.left)
    (hx : x ≫ U.forgetAuxiliary.data.polarized.abelian.scheme.hom = f.left)
    (hy : y ≫ U.forgetAuxiliary.data.polarized.abelian.scheme.hom = f'.left)
    (he : U.prescribedPointTransport hU π hk f g hfg x hx = y) :
    U.prescribedPointTransport hU π hk f j hfj' x hx =
      U.prescribedPointTransport hU π hk f' j hfj y hy := by
  subst f'
  subst y
  exact (U.prescribedPointTransport_trans hU π hk hrigid f g j hfg hfj x hx).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
