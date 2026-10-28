import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.IncidenceChartRecognition

/-! # Incidence Condition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.IncidenceCondition

noncomputable section

/-!
An intrinsic incidence condition expressed by quotient kernels in every local
normalized description. The constructed global ideal represents this condition.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ]
variable {S : Scheme.{u}} {M T : Over S}
variable (q : M ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S)
variable (k : M ⟶ ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S)
variable (F : Matrix μ ν Γ(M.left, ⊤))

def GrassmannIncidenceCondition (x : T ⟶ M) : Prop :=
  ∀ (U : Over S) (u : U ⟶ T) (a : ι → ν) (b : κ → μ)
    (v : U ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S) (w : U ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart b S),
    v ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S = u ≫ x ≫ q →
    w ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap b S = u ≫ x ≫ k →
      (Matrix.toLin' (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S v)).ker ≤
        ((Matrix.toLin' (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix b S w)).ker).comap
          (Matrix.toLin' (F.map (u ≫ x).left.appTop.hom))

omit [Fintype κ] in
theorem grassmannChartIncidenceIdeal_eq_bot_iff (a : ι → ν) (b : κ → μ)
    (v : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S) (w : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart b S) :
    ChartLoci.grassmannChartIncidenceIdeal a b v w F = ⊥ ↔
      (Matrix.toLin' (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S v)).ker ≤
        ((Matrix.toLin' (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix b S w)).ker).comap (Matrix.toLin' F) := by
  have h := ChartLoci.grassmannChartIncidenceIdeal_vanish_iff a b v w F (𝟙 M)
  change (ChartLoci.grassmannChartIncidenceIdeal a b v w F).comap (𝟙 M.left) = ⊥ ↔ _ at h
  rw [Scheme.IdealSheafData.comap_id, Category.id_comp, Category.id_comp] at h
  exact h

theorem grassmannIncidenceIdeal_vanish_iff (x : T ⟶ M) :
    (IncidenceScheme.grassmannIncidenceIdeal q k F).comap x.left = ⊥ ↔ GrassmannIncidenceCondition q k F x := by
  constructor
  · intro h U u a b v w hv hw
    let Fx := F.map x.left.appTop.hom
    have hx : IncidenceScheme.grassmannIncidenceIdeal (x ≫ q) (x ≫ k) Fx = ⊥ :=
      (IncidenceChartRecognition.grassmannIncidenceIdeal_baseChange F x).symm.trans h
    have hu : IncidenceScheme.grassmannIncidenceIdeal (u ≫ x ≫ q) (u ≫ x ≫ k)
        (Fx.map u.left.appTop.hom) = ⊥ :=
      (IncidenceChartRecognition.grassmannIncidenceIdeal_baseChange Fx u).symm.trans
        ((congrArg (fun I : T.left.IdealSheafData => I.comap u.left) hx).trans
          (Scheme.IdealSheafData.comap_bot u.left))
    have hc := (PairChartCover.grassmannPairChartCover (u ≫ x ≫ q) (u ≫ x ≫ k)).incidenceIdeal_eq_chart
      (Fx.map u.left.appTop.hom) a b v w hv hw
    exact (grassmannChartIncidenceIdeal_eq_bot_iff (Fx.map u.left.appTop.hom) a b v w).mp
      (hc.symm.trans hu)
  · intro h
    let D := PairChartCover.grassmannPairChartCover (x ≫ q) (x ≫ k)
    let Fx := F.map x.left.appTop.hom
    have hx : IncidenceScheme.grassmannIncidenceIdeal (x ≫ q) (x ≫ k) Fx = ⊥ := by
      apply ClosedFamily.OpenEquality.ideal_eq_of_open_cover D.cover
      intro i
      let c := Embedded.FamilyOpenCover.overOpenCoverMap T D.cover i
      have hc := h (Embedded.FamilyOpenCover.overOpenCoverObject T D.cover i) c (D.sourceColumns i) (D.targetColumns i)
        (D.sourceLift i) (D.targetLift i) (D.source_fac i) (D.target_fac i)
      have hi : D.incidenceLocalIdeal Fx i = ⊥ :=
        (grassmannChartIncidenceIdeal_eq_bot_iff (Fx.map c.left.appTop.hom)
          (D.sourceColumns i) (D.targetColumns i) (D.sourceLift i) (D.targetLift i)).mpr hc
      exact (D.incidenceIdeal_comap Fx i).trans
        (hi.trans (Scheme.IdealSheafData.comap_bot (D.cover.f i)).symm)
    exact (IncidenceChartRecognition.grassmannIncidenceIdeal_baseChange F x).trans hx

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.IncidenceCondition
