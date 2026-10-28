import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.Relabel
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.Reconstruction

/-! # Label Transitivity -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded

noncomputable section

/-! Two auxiliary markings on isomorphic prescribed PEL families
differ by an actual locally constant change of labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {T : Over (Spec (.of R))}

theorem PELId.IntegralAddedPELLevel.exists_relabel_of_prescribed_iso (A B : PELId.IntegralAddedPELLevel P R iotaO L N T)
    (e : PEL.Iso.PolarizedActionIso A.forgetAuxiliary.data B.forgetAuxiliary.data) :
    ∃ b : LocallyConstant T.left (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L),
      Nonempty (PELId.IntegralAddedPELLevel.Iso (A.relabelAuxiliary b) B) := by
  let α := @AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.transport (3 * s) L T.left
    A.auxiliary.data.polarized.abelian B.auxiliary.data.polarized.abelian
    A.auxiliary.data.polarized.level e.polarized.abelian e.polarized.abelianGroup
  let b := α.labelsEquiv B.auxiliary.data.polarized.level
  refine ⟨b, ⟨PELId.IntegralAddedPELLevel.Iso.of_forgetAuxiliary e ?_⟩⟩
  exact (@AbelianModuli.ReferenceFamily.Level.IsoCalculus.relabelFullLevel_transport T.left (3 * s) L
    A.auxiliary.data.polarized.abelian B.auxiliary.data.polarized.abelian inferInstance
    A.auxiliary.data.polarized.level b e.polarized.abelian e.polarized.abelianGroup).trans
    (α.labelsEquiv.symm_apply_apply B.auxiliary.data.polarized.level)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded
