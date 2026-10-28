import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionRatios
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.EvaluationTransport

/-! # Extended Chart Generators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExtendedChartGenerators

noncomputable section

/-!
Global extensions of a generating family make the corresponding powered
denominator chart evaluation surjective.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} {L : Line.Bundles.LineBundle X}

/-- Realizing chart generators as global power numerators gives a surjective
coordinate map on the chart of the powered denominator. -/
theorem extended_generators_chart_surjective (f : X ⟶ S)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (d : ℕ) (hd : 0 < d) {n : ℕ}
    (q : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ TensorPower.PowerSheaf.tensorPowerModule L.sheaf d))
    (i : Fin (n + 1)) (hi : q i = TensorPower.Maps.tensorPowerSection s d)
    (k : ℕ) (r : Fin k → Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤))
    (hr : letI := ((Ample.LineBundles.sectionNonvanishing s).ι ≫ f).appTop.hom.toAlgebra
      Algebra.adjoin Γ(S, ⊤) (Set.range r) = ⊤)
    (hext : ∀ j, ∃ l, Global.SectionExtension.PowerExtends s (r j) d (q l)) :
    Function.Surjective
      (ProjectiveChart.Evaluation.projectiveChartEvaluation ((Ample.LineBundles.sectionNonvanishing (q i)).ι ≫ f).appTop.hom
        (fun l => Section.Frames.sectionRatio (q i) (q l)) i (Section.Frames.sectionRatio_self (q i))) := by
  let D := Ample.LineBundles.sectionNonvanishing s
  have hD : Ample.LineBundles.sectionNonvanishing (q i) = D :=
    (congrArg Ample.LineBundles.sectionNonvanishing hi).trans (Section.PowerLocus.sectionNonvanishing_tensorPowerSection s d hd)
  let b := (X.isoOfEq hD).inv.appTop.hom
  let := (D.ι ≫ f).appTop.hom.toAlgebra
  have hb : Function.Injective b :=
    (ConcreteCategory.bijective_of_isIso (Scheme.Γ.map (X.isoOfEq hD).inv.op)).1
  have hc : b.comp ((Ample.LineBundles.sectionNonvanishing (q i)).ι ≫ f).appTop.hom =
      algebraMap Γ(S, ⊤) Γ(D.toScheme, ⊤) := Power.SectionRatios.equal_open_appTop_coefficients f hD
  have hp : IsIso (Ample.LineBundles.pullbackSection D.ι (TensorPower.Maps.tensorPowerSection s d)) :=
    Power.Nonvanishing.tensorPowerSection_pullback_isIso D.ι s d
  have hqi : IsIso (Ample.LineBundles.pullbackSection D.ι (q i)) :=
    (congrArg (fun t => IsIso (Ample.LineBundles.pullbackSection D.ι t)) hi).mpr hp
  have hcontains (j : Fin k) : ∃ l, b (Section.Frames.sectionRatio (q i) (q l)) = r j := by
    obtain ⟨l, hl⟩ := hext j
    refine ⟨l, (Power.SectionRatios.sectionRatio_on_equal_open (q i) (q l) D hD).trans ?_⟩
    exact (Frame.FrameRestriction.frameCoordinate_congr (congrArg (Ample.LineBundles.pullbackSection D.ι) hi) rfl).trans hl
  exact Chart.EvaluationTransport.projectiveChartEvaluation_surjective_after_embedding b hb
    ((Ample.LineBundles.sectionNonvanishing (q i)).ι ≫ f).appTop.hom hc
    (fun l => Section.Frames.sectionRatio (q i) (q l)) i (Section.Frames.sectionRatio_self (q i))
    (Chart.EvaluationTransport.adjoin_range_eq_top_of_contains r (fun l => b (Section.Frames.sectionRatio (q i) (q l))) hr hcontains)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExtendedChartGenerators
