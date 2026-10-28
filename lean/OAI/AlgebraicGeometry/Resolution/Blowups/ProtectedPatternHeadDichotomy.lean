import OAI.AlgebraicGeometry.Resolution.Blowups.PatternComparisonHeadCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.WholeOrEmptyCenter

/-! # Protected Pattern Head Dichotomy -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedPatternHeadDichotomy.Construction

noncomputable section

/-! On a protected integral carrier, the actual first center is either the whole protected carrier or empty. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem protected_pattern_head_center_dichotomy
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {K : Y.IdealSheafData}
    (C : X.IdealSheafData) (hC : C ≠ ⊥) (hp : J ≤ C ^ 1)
    (hs : Smooth (C.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f))
    (tail : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 (GlobalBlowup.Data.Construction.globalBlowup C hC) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C J hC 1) Y g K)
    (O : X.Opens) [IsIntegral (J.comap O.ι).subscheme]
    (A : ProtectedPatternChart.Construction.ProtectedPatternProgramCover (.blowup C hC (by decide) hp hs hbl tail) O) :
    C.comap O.ι = J.comap O.ι ∨ C.comap O.ι = ⊤ := by
  have hJC : J ≤ C := by simpa only [pow_one] using hp
  apply Locally.WholeOrEmptyCenter.Construction.idealSheaf_eq_or_top_of_pointed_whole_or_empty_charts (J.comap O.ι) (C.comap O.ι)
    (Scheme.IdealSheafData.comap_mono O.ι hJC)
  intro x hx
  have hxJ : O.ι x ∈ J.support := by
    rw [Scheme.IdealSheafData.support_comap] at hx
    exact hx
  obtain ⟨i, p, hp⟩ := A.cover (O.ι x) hxJ x.property
  let B := A.chart i
  have hrange : Set.range B.map ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    rintro y ⟨z, rfl⟩
    exact B.contained z
  let j := IsOpenImmersion.lift O.ι B.map hrange
  have hj : j ≫ O.ι = B.map := IsOpenImmersion.lift_fac _ _ _
  let : IsOpenImmersion (j ≫ O.ι) := hj.symm ▸ B.isOpenImmersion
  let : IsOpenImmersion j := IsOpenImmersion.of_comp j O.ι
  refine ⟨B.source, j, inferInstance, p, ?_, ?_⟩
  · apply O.ι.isOpenEmbedding.injective
    exact (congrArg (fun q => q p) hj).trans hp
  · have hchoice := Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.head_center_dichotomy_of_pattern_comparison
      C hC (by simpa only [pow_one] using hJC) hs hbl tail B.modelProgram B.commonProgram
      B.map B.globalEndMap B.modelMap B.modelEndMap B.globalComparison B.modelComparison B.modelPattern
    simpa only [← Scheme.IdealSheafData.comap_comp, hj] using hchoice

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedPatternHeadDichotomy.Construction
