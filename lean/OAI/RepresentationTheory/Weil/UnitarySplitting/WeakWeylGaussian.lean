import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylSynthesisAdd

/-! # Weak Weyl Gaussian -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.WeakWeylGaussian.Construction

noncomputable section

/-! An absolutely convergent weak Gaussian transform of Weyl matrix
coefficients. This uses the actual Schrödinger action on test functions. -/

open _root_.MeasureTheory _root_.Topology

def weakWeylGaussian
    {F : Type} [NormedField F] [MeasurableSpace F] {d : ℕ}
    (ψ : AddChar F ℂ) (μ : Measure (Local.FunctionsMetaplectic.Construction.Position F d)) (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d))
    (q : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → F) (f h : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) : ℂ :=
  ∫ v, ψ (q v) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f h v ∂ν

theorem weakWeylGaussian_integrable_ultra
    {F : Type} [NormedField F] [LocallyCompactSpace F] [IsUltrametricDist F]
    [MeasurableSpace F] [BorelSpace F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x))
    (hn : ∃ a : F, ψ a ≠ 1)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position F d)) [μ.IsAddHaarMeasure]
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) [ν.IsAddHaarMeasure]
    (q : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → F) (hq : Continuous q) (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    Integrable (fun v => ψ (q v) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val h.val v) ν := by
  let : SecondCountableTopology F := TestSpaceAnalysis.Construction.localField_secondCountable F hF
  have hc' := (hc.comp hq).mul (UltraWeylCoefficients.Construction.weylMatrixCoefficient_locallyConstant_ultra hF ψ hc μ f h).continuous
  exact hc'.integrable_of_hasCompactSupport
    (WeylSynthesisAdd.Construction.weylMatrixCoefficient_compactSupport_ultra hF ψ hn μ f h).mul_left

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.WeakWeylGaussian.Construction
