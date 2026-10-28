import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.Freeness
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.AutomorphismDescent

/-! # Rigidity Pullback -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Prescribed-level rigidity persists under arbitrary parameter
pullback, including restriction to the actual reduction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Y : Over (Spec (.of R))}

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedRigid_pullback (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)
    (hU : U.PrescribedRigid) (f : Y ⟶ X) : (U.pullback f).PrescribedRigid := by
  intro T _ g e
  apply AbelianModuli.ReferenceFamily.Pure.AutomorphismDescent.pure_abelian_eq_id_via e
    (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp U.forgetAuxiliary.data.polarized f.left g.left)
  intro a
  exact hU T (g ≫ f) a

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
