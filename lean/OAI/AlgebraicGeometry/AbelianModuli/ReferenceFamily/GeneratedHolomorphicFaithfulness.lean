import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionComparisonRegularOpens
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RegularGaugeGluing

/-! # Generated Holomorphic Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Equal native holomorphic classes of algebraic line bundles with
generating sections give an isomorphism of their original algebraic
sheaves. The regular gauges come from the algebraized combined map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates
open scoped _root_.Manifold ContDiff

theorem GeneratedHolomorphicFaithfulness.comparisonGauge_inverse_relation (a b c d : ℂ) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : a / b = d / c) : b * (1 / c) = (1 / d) * a := by
  have h := (div_eq_div_iff hb hc).mp he
  field_simp [hc, hd]
  exact (mul_comm b d).trans (h.symm.trans (mul_comm a c))

section

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier} {n m : ℕ}
    {s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ L.sheaf)}
    {t : Fin (m + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ K.sheaf)}
    {hs : ∀ x : V.carrier, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)}
    {ht : ∀ x : V.carrier, ∃ j, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t j)}
    (A : SectionComparisonVectors.SectionComparisonAlgebraization V s t hs ht)

include A in
theorem SectionComparisonVectors.SectionComparisonAlgebraization.algebraicIso : Nonempty (K.sheaf ≅ L.sheaf) := by
  have hL : ∀ i, A.regularOpen i ≤ (SectionLocalFrames.sectionLocalFrame (s i.1)).domain :=
    fun i => (A.regularOpen_eq i).le.trans inf_le_left
  have hK : ∀ i, A.regularOpen i ≤ (SectionLocalFrames.sectionLocalFrame (t i.2)).domain :=
    fun i => (A.regularOpen_eq i).le.trans inf_le_right
  apply Intrinsic.RegularGaugeGluing.exists_iso_of_native_regular_gauges V K L A.regularOpen A.regularOpen_covers
    (fun i => SectionLocalFrames.sectionLocalFrame (t i.2)) (fun i => SectionLocalFrames.sectionLocalFrame (s i.1)) hK hL A.regularUnit
  intro i j x hi hj
  have hi' := (A.regularOpen_mem i x).mp hi
  have hj' := (A.regularOpen_mem j x).mp hj
  have hrL := (Intrinsic.SectionCoordinates.nativeSectionCoordinates_ratio V.presentation s hs i.1 j.1 x hi'.1).trans
    (SectionFrameEvaluation.sectionFrame_pointTransition V.presentation (s i.1) (s j.1) x hi'.1 hj'.1).symm
  have hrK := (Intrinsic.SectionCoordinates.nativeSectionCoordinates_ratio V.presentation t ht i.2 j.2 x hi'.2).trans
    (SectionFrameEvaluation.sectionFrame_pointTransition V.presentation (t i.2) (t j.2) x hi'.2 hj'.2).symm
  have he := (congrArg₂ (· / ·) hrL hrK).symm.trans (A.gauge_law i j x hi' hj')
  erw [A.regularUnit_value i x hi, A.regularUnit_value j x hj]
  exact GeneratedHolomorphicFaithfulness.comparisonGauge_inverse_relation _ _ _ _
    (AnalyticFrameTransitions.frameTransitionPair_ne_zero V.presentation (SectionLocalFrames.sectionLocalFrame (t i.2)) (SectionLocalFrames.sectionLocalFrame (t j.2))
      ⟨x, hi'.2, hj'.2⟩)
    (DivisorClass.Chern.Holomorphic.SlitLog.holomorphicUnit_value_ne_zero (A.gauge i) ⟨x, hi'⟩)
    (DivisorClass.Chern.Holomorphic.SlitLog.holomorphicUnit_value_ne_zero (A.gauge j) ⟨x, hj'⟩) he

end

theorem GeneratedHolomorphicFaithfulness.generatedLineBundles_iso_of_holomorphicClass_eq (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier) {n m : ℕ}
    (s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ L.sheaf))
    (t : Fin (m + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ K.sheaf))
    (hs : ∀ x : V.carrier, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ x : V.carrier, ∃ j, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t j))
    (he : Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass V L = Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass V K) :
    Nonempty (L.sheaf ≅ K.sheaf) := by
  obtain ⟨A⟩ := SectionComparisonVectors.sectionComparisonAlgebraization_nonempty V s t hs ht he
  obtain ⟨e⟩ := A.algebraicIso
  exact ⟨e.symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
