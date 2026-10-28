import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ActionBaseChangeComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieRankRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso

/-! # Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Transport an actual integral PEL object through an isomorphism of its
polarized family, retaining the arithmetic Lie condition in every characteristic. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {T : Over (Spec (.of R))}

def PEL.Has.IntegralPELObject.transport (A : PEL.Has.IntegralPELObject P R iotaO N T)
    {B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N T.left}
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A.data.polarized B) : PEL.Has.IntegralPELObject P R iotaO N T where
  data := { polarized := B, action := ActionBaseChangeComparison.transportIntegralAction e.abelian A.data.action }
  rosati := (RosatiRestriction.rosati_iff_of_polarized_iso e A.data.action _ (fun a => by
    change e.abelian.hom ≫ (e.abelian.inv ≫ A.data.action.map a ≫ e.abelian.hom) = _
    exact Iso.hom_inv_id_assoc _ _)).mp A.rosati
  lieRanks := (Integral.LieRankRestriction.integralLieRanks_iff_of_iso P iotaO T A.data.action _ e.abelian (fun a => by
    change A.data.action.map a ≫ e.abelian.hom =
      e.abelian.hom ≫ (e.abelian.inv ≫ A.data.action.map a ≫ e.abelian.hom)
    exact (Iso.hom_inv_id_assoc _ _).symm)).mp A.lieRanks

def PEL.Has.IntegralPELObject.transportIso (A : PEL.Has.IntegralPELObject P R iotaO N T)
    {B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N T.left}
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A.data.polarized B) :
    PEL.Iso.PolarizedActionIso A.data (A.transport e).data where
  polarized := e
  action a := (Iso.hom_inv_id_assoc e.abelian (A.data.action.map a ≫ e.abelian.hom)).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
