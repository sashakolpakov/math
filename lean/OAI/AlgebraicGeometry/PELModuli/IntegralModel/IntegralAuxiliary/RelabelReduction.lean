import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.FineReduction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.Automorphisms
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.InvariantAffineCover

/-! # Relabel Reduction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! A relabeling comparison on a possibly nonreduced parameter induces
exactly the classifying relabeling map of its reduced universal family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}

theorem IntegralAdded.PELId.IntegralAddedPELLevel.reduced_relabel_map_eq (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (σ : AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L) (a : X ⟶ X)
    (e : IntegralAdded.PELId.IntegralAddedPELLevel.Iso (U.pullback a) (U.relabelAuxiliary (LocallyConstant.const _ σ))) :
    Reduced.InvariantAffineCover.reducedEndomorphism a = (U.pullback (Reduction.reductionι X)).auxiliaryRelabelMap
      (IntegralAdded.FineReduction.integralAddedPEL_fine_reduction U hU) σ := by
  apply (U.pullback (Reduction.reductionι X)).classifying_unique (IntegralAdded.FineReduction.integralAddedPEL_fine_reduction U hU)
    (Reduction.reduction X) ((U.pullback (Reduction.reductionι X)).relabelAuxiliary (LocallyConstant.const _ σ))
    (Reduced.InvariantAffineCover.reducedEndomorphism a)
  exact (U.pullbackCompIso (Reduction.reductionι X) (Reduced.InvariantAffineCover.reducedEndomorphism a)).trans
    ((U.pullbackCongrIso _ _ (Reduced.InvariantAffineCover.reducedEndomorphism_ι a)).trans
      ((U.pullbackCompIso a (Reduction.reductionι X)).symm.trans
        ((e.pullback (Reduction.reductionι X)).trans
          (IntegralAdded.PELId.IntegralAddedPELLevel.Iso.ofEq (U.relabelAuxiliary_pullback (LocallyConstant.const _ σ) (Reduction.reductionι X))))))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
