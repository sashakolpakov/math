import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.ChartPullback

/-! # Immersion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.Immersion.GradedHilbert

noncomputable section

/-! The global bounded Hilbert parameter map is a quasi-compact locally
closed immersion, as checked on the actual Grassmannian open atlas. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] (n N : ℕ) (S : Scheme.{u}) (q : ℕ → ℕ)

instance boundedHilbertParameter_chart_isImmersion (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) :
    IsImmersion (pullback.snd (Data.GradedHilbert.boundedHilbertParameter (ι := ι) n N S q) (Grassmannian.Gluing.grassmannianChartMap a S)) := by
  let hp := ChartPullback.GradedHilbert.boundedHilbertChart_isPullback a S q
  have h : IsImmersion (hp.isoPullback.inv ≫ (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartInclusion a S q).left) := inferInstance
  rw [hp.isoPullback_inv_snd] at h
  exact h

instance boundedHilbertParameter_isImmersion : IsImmersion (Data.GradedHilbert.boundedHilbertParameter (ι := ι) n N S q) := by
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsImmersion)
    (Grassmannian.Gluing.normalizedGrassmannianGlueData (ι := ι) (ν := Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S).openCover).mpr
  intro a
  change ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N at a
  exact boundedHilbertParameter_chart_isImmersion n N S q a

instance boundedHilbertParameter_chart_quasiCompact (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) :
    QuasiCompact (pullback.snd (Data.GradedHilbert.boundedHilbertParameter (ι := ι) n N S q) (Grassmannian.Gluing.grassmannianChartMap a S)) := by
  let hp := ChartPullback.GradedHilbert.boundedHilbertChart_isPullback a S q
  have h : QuasiCompact (hp.isoPullback.inv ≫ (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartInclusion a S q).left) := inferInstance
  rw [hp.isoPullback_inv_snd] at h
  exact h

instance boundedHilbertParameter_quasiCompact : QuasiCompact (Data.GradedHilbert.boundedHilbertParameter (ι := ι) n N S q) := by
  have : IsZariskiLocalAtTarget @QuasiCompact.{u} :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @QuasiCompact)
    (Grassmannian.Gluing.normalizedGrassmannianGlueData (ι := ι) (ν := Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S).openCover).mpr
  intro a
  change ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N at a
  exact boundedHilbertParameter_chart_quasiCompact n N S q a

theorem bounded_hilbert_functor_immersion :
    SubfunctorRepresentations.ImmersionRepresentable (Representation.GradedHilbert.boundedHilbertSubfunctor (ι := ι) n N S q) :=
  ⟨Data.GradedHilbert.boundedHilbertOver n N S q, Data.GradedHilbert.boundedHilbertParameterOver n N S q,
    boundedHilbertParameter_isImmersion n N S q, boundedHilbertParameter_quasiCompact n N S q,
    Representation.GradedHilbert.bounded_hilbert_scheme_representation n N S q⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.Immersion.GradedHilbert
