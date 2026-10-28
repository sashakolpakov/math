import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FinePELCountableImages
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FinePELDimension
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SmoothStrata
import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.ImageMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! # Fine PEL Surface Stratum -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! A finite-type fine PEL model contains an actual smooth integral
surface stratum meeting the prescribed reference locus. Its dimension
comes from the countable reference-period cover and the upper bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MeasureTheory _root_.MeasureTheory.Measure
open scoped Classical

open OAI.RepresentationTheory.Theta.Geometric.Holomorphic.ImageMeasure

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    [LocallyOfFiniteType M.space.hom] [QuasiCompact M.space.hom]

include hM hκ in
theorem Models.FinePELModel.exists_reference_smooth_surface_stratum
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    ∃ R : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece (M.complexFiber κ).hom,
      R.complexDimension = 2 ∧ ∃ (a : P.domain) (x : R.analyticSpace),
        x ≫ Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) R = M.referencePoint hM κ hP hκ a := by
  have : LocallyOfFiniteType (M.complexFiber κ).hom := M.complexFiber_locallyFiniteType κ
  have : QuasiCompact (M.complexFiber κ).hom :=
    inferInstanceAs (QuasiCompact (Limits.pullback.snd M.space.hom (Spec.map (CommRingCat.ofHom κ))))
  have : SecondCountableTopology (M.ComplexPoints κ) := AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeSchemeTopology.schemePoints_secondCountable (M.complexFiber κ)
  let Q := CycleClass.Geometric.IntegralSmoothStratification.integralSmoothGeometricStratification_of_finiteType (M.complexFiber κ).hom
  let R (j : Fin Q.pieces.length) := Q.pieces.get j
  let f (j : Fin Q.pieces.length) := Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) (R j)
  have (j : Fin Q.pieces.length) : SecondCountableTopology (R j).analyticSpace :=
    Intrinsic.SmoothStrata.smoothPiece_secondCountable (M.complexFiber κ) (R j)
  have hex (j : Fin Q.pieces.length) := M.exists_countable_reference_images hM κ hP hκ (f j)
  choose I hI O period hO hcover using hex
  have (j : Fin Q.pieces.length) : Countable (I j) := hI j
  let hit (j : Fin Q.pieces.length) := ∃ (a : P.domain) (x : (R j).analyticSpace),
    x ≫ f j = M.referencePoint hM κ hP hκ a
  have hlarge : ∃ j : Fin Q.pieces.length, 2 ≤ (R j).complexDimension ∧ hit j := by
    by_contra hn
    have hsmall (j : Fin Q.pieces.length) (hj : hit j) : (R j).complexDimension < 2 :=
      lt_of_not_ge (fun hd => hn ⟨j, hd, hj⟩)
    let J := {i : (Σ j : Fin Q.pieces.length, I j) // hit i.1}
    let μ : Measure Geometry.ComplexBall.PrescribedSignsB.BallChart := volume
    have hzero (i : J) : μ (period i.val.1 i.val.2 '' O i.val.1 i.val.2) = 0 := by
      apply RepresentationTheory.Theta.Geometric.Holomorphic.ImageMeasure.measure_image_eq_zero_of_complex_finrank_lt μ (hO i.val.1 i.val.2).1 (hO i.val.1 i.val.2).2
      have hd : Betti.AffineDimension.Realization.functionFieldDifferentialDimension (R i.val.1).toOver.hom < 2 := by
        rw [Intrinsic.SmoothStrata.smoothPiece_dimension (M.complexFiber κ) (R i.val.1)]
        exact hsmall i.val.1 i.property
      simpa only [Geometry.ComplexBall.PrescribedSignsB.BallChart, Module.finrank_pi, Fintype.card_fin] using hd
    have hnull : μ P.domain = 0 := by
      apply measure_mono_null (t := ⋃ i : J, period i.val.1 i.val.2 '' O i.val.1 i.val.2) ?_
        (measure_iUnion_null hzero)
      intro a ha
      obtain ⟨j, x, hx⟩ := Intrinsic.SmoothStrata.smoothStratification_complexPoint_cover (M.complexFiber κ) Q
        (M.referencePoint hM κ hP hκ ⟨a, ha⟩)
      obtain ⟨i, hi⟩ := hcover j ⟨a, ha⟩ ⟨x, hx⟩
      exact Set.mem_iUnion.mpr ⟨⟨⟨j, i⟩, ⟨⟨a, ha⟩, x, hx⟩⟩, hi⟩
    have hne : P.domain.Nonempty := ⟨(P.referenceOrigin hP).val, (P.referenceOrigin hP).property⟩
    exact (ne_of_gt (P.domain_isOpen.measure_pos (μ := μ) hne)) hnull
  obtain ⟨j, hj, a, x, hx⟩ := hlarge
  have hu := M.smooth_subspace_dimension_le_two hM κ hκ (f j) x hs hdegree hP
    (Nat.pos_of_ne_zero (NeZero.ne N))
  rw [Intrinsic.SmoothStrata.smoothPiece_dimension (M.complexFiber κ) (R j)] at hu
  exact ⟨R j, Nat.le_antisymm hu hj, a, x, hx⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
