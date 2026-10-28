import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.Automorphisms
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.FineBaseChange

/-! # Relabel Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The constructed auxiliary relabeling automorphisms commute with
coefficient extension, by their actual universal family comparisons. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R R' : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [CommRing R'] {s L N : ℕ} [NeZero L]
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iotaO : NumberField.RingOfIntegers E →+* R}
    {X : Over (Spec (.of R))} [IsReduced X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine) (φ : R →+* R')
    [IsReduced ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).left]

theorem IntegralAdded.PELId.IntegralAddedPELLevel.auxiliaryRelabelMap_baseChange (σ : AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L) :
    (Over.pullback (Spec.map (CommRingCat.ofHom φ))).map (U.auxiliaryRelabelMap hU σ) =
      (U.baseChange φ).auxiliaryRelabelMap (IntegralAdded.FineBaseChange.integralAddedPEL_fine_baseChange U hU φ) σ := by
  let X' := (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X
  let f := U.auxiliaryRelabelMap hU σ
  let f' := (Over.pullback (Spec.map (CommRingCat.ofHom φ))).map f
  let A := (U.baseChange φ).relabelAuxiliary (LocallyConstant.const _ σ)
  apply (U.baseChange φ).classifying_unique (IntegralAdded.FineBaseChange.integralAddedPEL_fine_baseChange U hU φ) X' A f'
  apply Classical.choice
  apply (IntegralAdded.ScalarChange.integralAddedPEL_baseChange_classifying_iff φ U X' A f').mpr
  let b := Spec.map (CommRingCat.ofHom φ)
  let g : PEL.ScalarRestriction.coefficientRestriction φ X' ⟶ X := Over.homMk (pullback.fst X.hom b) pullback.condition
  let k := ((Over.mapPullbackAdj b).homEquiv X' X).symm f'
  have hk : k = g ≫ f := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  exact ⟨(U.pullbackCongrIso k (g ≫ f) hk).trans (U.auxiliaryRelabelPullbackComparison hU g σ)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
