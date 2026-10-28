import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.LogUnitClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.Add
import OAI.AlgebraicGeometry.DivisorClass.Chern.ContinuousGauge

/-! # Log Class Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.LogClassComparison

noncomputable section

/-! Equality of the actual holomorphic unit-sheaf classes forces equality
of the original logarithmic singular Chern classes. The comparison uses
the constructed holomorphic change of trivialization. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.ContinuousGauge.RationalCech
open scoped _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]
  {I : Type} (U : I → Opens M)

theorem holomorphicUnitCech_boundary_gauge
    (k k' : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj U 1)
    (b : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj U 0)
    (hb : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj U 0 b = k' - k) :
    ∃ g : ∀ i, C(U i, ℂ), (∀ i x, g i x ≠ 0) ∧
      ∀ (a : Fin 2 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
        (LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k' a)).val x =
          (LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k a)).val x *
            g (a 1) ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property⟩ /
              g (a 0) ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property⟩ := by
  let F := DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M
  obtain ⟨s, hs⟩ := Cech.Add.cech_zero_eq_localSections (X := TopCat.of M) U F b
  let u (i : I) := LogUnitClass.holomorphicUnitSection E M (U i) (s i)
  let g (i : I) : C(U i, ℂ) :=
    ⟨(u i).val, (u i).val.property.continuous⟩
  have hg : ∀ i x, g i x ≠ 0 := fun i x => DivisorClass.Chern.Holomorphic.SlitLog.holomorphicUnit_value_ne_zero (u i) x
  refine ⟨g, hg, ?_⟩
  intro a x
  have hd := congrFun hb a
  rw [← hs, DivisorClass.Chern.Cech.LocalSections.abelianCechLocalSections_delta] at hd
  have hv := congrArg (fun z : F.obj.obj (.op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) =>
    (LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) z).val x) hd
  change (LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (_ - _)).val x =
    (LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k' a - k a)).val x at hv
  rw [LogUnitClass.holomorphicUnitSection_value_sub, LogUnitClass.holomorphicUnitSection_value_sub] at hv
  change g (a 1) ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property⟩ /
      g (a 0) ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property⟩ =
    (LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k' a)).val x /
      (LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k a)).val x at hv
  calc
    (LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k' a)).val x =
        ((LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k' a)).val x /
          (LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k a)).val x) *
            (LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k a)).val x :=
      (div_mul_cancel₀ _ (DivisorClass.Chern.Holomorphic.SlitLog.holomorphicUnit_value_ne_zero
        (LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k a)) x)).symm
    _ = _ := by rw [← hv]; ring

theorem logarithmicChern_eq_of_holomorphicClass_eq
    (hU : ∀ x, ∃ i, x ∈ U i)
    (l l' : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain (TopCat.of M) U)
    (hl : ∀ a, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ) ∞ (l a))
    (hl' : ∀ a, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ) ∞ (l' a))
    (h : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle (TopCat.of M) U l)
    (h' : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle (TopCat.of M) U l')
    (he : LogUnitClass.holomorphicLogUnitClass E M U l' hl' h' hU =
      LogUnitClass.holomorphicLogUnitClass E M U l hl h hU) :
    DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass (TopCat.of M) U hU l' h' =
      DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass (TopCat.of M) U hU l h := by
  let k := LogUnitClass.holomorphicLogUnitCech E M U l hl
  let k' := LogUnitClass.holomorphicLogUnitCech E M U l' hl'
  obtain ⟨b, hb⟩ := Cech.Add.cech_one_difference_boundary (X := TopCat.of M) U (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M)
    (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of M) U hU) k' k
    (LogUnitClass.holomorphicLogUnitCech_closed E M U l' hl' h')
    (LogUnitClass.holomorphicLogUnitCech_closed E M U l hl h) he
  obtain ⟨g, hg, htrans⟩ := holomorphicUnitCech_boundary_gauge E M U k k' b hb
  exact DivisorClass.Chern.ContinuousGauge.RationalCech.logarithmicSingularClass_continuous_gauge (TopCat.of M) U g hg hU l l' h h' htrans

theorem holomorphic_refineLogCech {J : Type} (V : J → Opens M) (r : J → I)
    (hr : ∀ j, V j ≤ U (r j)) (l : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain (TopCat.of M) U)
    (hl : ∀ a, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ) ∞ (l a)) (a : Fin 2 → J) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ) ∞ (DivisorClass.Chern.LogRefinement.RationalCech.refineLogCech (TopCat.of M) U V r hr l a) :=
  (hl (r ∘ a)).comp (contMDiff_inclusion (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_refinement_le U V r hr a))

theorem holomorphicLogUnitClass_refinement {J : Type} (V : J → Opens M) (r : J → I)
    (hr : ∀ j, V j ≤ U (r j))
    (hU : ∀ x, ∃ i, x ∈ U i) (hV : ∀ x, ∃ j, x ∈ V j)
    (l : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain (TopCat.of M) U)
    (hl : ∀ a, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ) ∞ (l a))
    (h : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle (TopCat.of M) U l) :
    LogUnitClass.holomorphicLogUnitClass E M V (DivisorClass.Chern.LogRefinement.RationalCech.refineLogCech (TopCat.of M) U V r hr l)
      (holomorphic_refineLogCech E M U V r hr l hl)
      (DivisorClass.Chern.LogRefinement.RationalCech.exponentialCocycle_refinement (TopCat.of M) U V r hr l h) hV =
    LogUnitClass.holomorphicLogUnitClass E M U l hl h hU := by
  have he : DivisorClass.Chern.Cech.AbelianRefinement.abelianCechRefinementMap (X := TopCat.of M) U V r hr (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj 1
      (LogUnitClass.holomorphicLogUnitCech E M U l hl) =
    LogUnitClass.holomorphicLogUnitCech E M V (DivisorClass.Chern.LogRefinement.RationalCech.refineLogCech (TopCat.of M) U V r hr l)
      (holomorphic_refineLogCech E M U V r hr l hl) := by
    funext a
    apply Units.ext
    apply ContMDiffMap.ext
    intro x
    rfl
  have hc := DivisorClass.Chern.Cech.ClassRefinement.abelianCechSheafClass_refinement (X := TopCat.of M) U V r hr
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M) (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of M) U hU)
    (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of M) V hV)
    0 (LogUnitClass.holomorphicLogUnitCech E M U l hl) (LogUnitClass.holomorphicLogUnitCech_closed E M U l hl h)
  exact (Cech.Add.cechSheafClass_congr (X := TopCat.of M) V (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M)
    (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of M) V hV) 0 _ _
    (LogUnitClass.holomorphicLogUnitCech_closed E M V _ _
      (DivisorClass.Chern.LogRefinement.RationalCech.exponentialCocycle_refinement (TopCat.of M) U V r hr l h))
    (DivisorClass.Chern.Cech.ClassRefinement.abelianCechRefinementMap_closed (X := TopCat.of M) U V r hr (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj 1 _
      (LogUnitClass.holomorphicLogUnitCech_closed E M U l hl h)) he.symm).trans hc

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.LogClassComparison
