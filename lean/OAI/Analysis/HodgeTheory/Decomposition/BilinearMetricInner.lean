import OAI.Analysis.HodgeTheory.Decomposition.BilinearFormMetric
import OAI.Analysis.HodgeTheory.Decomposition.CoordinateMetric
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Bilinear Metric Inner -/

namespace OAI.Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions

noncomputable section

/-! The explicit induced form pairing is an ordinary finite-dimensional
complex inner product, giving its exact derivative in the covector arguments. -/

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

theorem bilinearFormMetricPair_eq_inner (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a c : DifferentialForms.Manifold.Basic.FormValue E n) :
    BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a c =
      inner ℂ (CoordinateMetric.Constructions.realMatrixOperator (BilinearFormMetric.Constructions.bilinearExteriorGram b n B)⁻¹ (SymbolDifferential.Constructions.exteriorCoordinateEquiv b n a))
        (SymbolDifferential.Constructions.exteriorCoordinateEquiv b n c) := by
  rw [CoordinateMetric.Constructions.realMatrixOperator_complex_inner]
  simp only [SymbolDifferential.Constructions.exteriorCoordinateEquiv_apply]
  rfl

theorem bilinearFormMetricPair_hasDerivAt (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a c : ℝ → DifferentialForms.Manifold.Basic.FormValue E n) (da dc : DifferentialForms.Manifold.Basic.FormValue E n)
    (t : ℝ) (ha : HasDerivAt a da t) (hc : HasDerivAt c dc t) :
    HasDerivAt (fun s => BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (a s) (c s))
      (BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (a t) dc + BilinearFormMetric.Constructions.bilinearFormMetricPair b n B da (c t)) t := by
  let Q := (SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).toContinuousLinearMap.restrictScalars ℝ
  let L := (CoordinateMetric.Constructions.realMatrixOperator (BilinearFormMetric.Constructions.bilinearExteriorGram b n B)⁻¹).comp Q
  have hleft : HasDerivAt (fun s => L (a s)) (L da) t := L.hasFDerivAt.comp_hasDerivAt t ha
  have hright : HasDerivAt (fun s => Q (c s)) (Q dc) t := Q.hasFDerivAt.comp_hasDerivAt t hc
  have h := hleft.inner ℂ hright
  convert! h using 1 <;> simp only [bilinearFormMetricPair_eq_inner] <;> rfl

end

end OAI.Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions
