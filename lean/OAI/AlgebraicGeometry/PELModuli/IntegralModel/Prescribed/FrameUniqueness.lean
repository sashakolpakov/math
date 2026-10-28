import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.Reconstruction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.IsoRigidity

/-! # Frame Uniqueness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Prescribed.FrameUniqueness

noncomputable section

/-! Rigidity fixes the ordered auxiliary marking under two comparisons
of the same prescribed-level PEL family. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {T : Over (Spec (.of R))}

theorem prescribedPEL_frame_eq (U : PEL.Has.IntegralPELObject P R iotaO N T)
    (hRigid : ∀ e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso U.data.polarized U.data.polarized,
      e.abelian.hom = 𝟙 U.data.polarized.abelian.scheme)
    (α β : U.data.polarized.abelian.FullLevel L)
    (A : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N T)
    (a : IntegralAdded.PELId.IntegralAddedPELLevel.Iso (IntegralAdded.PELId.IntegralAddedPELLevel.ofPrescribed U α) A)
    (b : IntegralAdded.PELId.IntegralAddedPELLevel.Iso (IntegralAdded.PELId.IntegralAddedPELLevel.ofPrescribed U β) A) : α = β := by
  have h := Polarized.IsoRigidity.polarizedIso_eq_of_source_rigidity hRigid a.forgetAuxiliary.polarized b.forgetAuxiliary.polarized
  have hab := congrArg (fun e => e.abelian.hom) h
  apply AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro V c
  apply (cancel_mono b.auxiliary.polarized.abelian.hom).mp
  exact ((congrArg (fun z => (α.hom.app (.op V) c).val ≫ z) hab).symm.trans
    (a.auxiliary.polarized.level V c)).trans (b.auxiliary.polarized.level V c).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Prescribed.FrameUniqueness
