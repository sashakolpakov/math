import OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

/-! # Radius Chart Conjugation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RadiusChartConjugation.TestTransport

noncomputable section

/-! Explicit radius normalization of the rank-three projective chart. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

open OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

variable {K : Type*} [Field K]

theorem radius_inverse_line (r : K) (hr : r ≠ 0) (z : Fin 2 → K) :
    (Matrix.diagonal ![(1 : K), 1, r⁻¹]) *ᵥ RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z = r⁻¹ • RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector (r • z) := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec_diagonal, RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector, hr]

theorem radius_chart_conjugation (g h : Matrix.SpecialLinearGroup (Fin 3) K)
    (r : K) (hr : r ≠ 0)
    (hh : h.val = Matrix.diagonal ![(1 : K), 1, r] * g.val *
      Matrix.diagonal ![(1 : K), 1, r⁻¹]) (z : Fin 2 → K) :
    RepresentationTheory.Theta.Adelic.DeterminantCoordinates.chartImage h z = r⁻¹ • RepresentationTheory.Theta.Adelic.DeterminantCoordinates.chartImage g (r • z) := by
  have hvec : h.val *ᵥ RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z =
      r⁻¹ • ((Matrix.diagonal ![(1 : K), 1, r]) *ᵥ (g.val *ᵥ RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector (r • z))) := by
    rw [hh, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, radius_inverse_line r hr,
      Matrix.mulVec_smul, Matrix.mulVec_smul]
  have hd : RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator h z = RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator g (r • z) := by
    have ht := congr_fun hvec 2
    simpa [RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator, Matrix.mulVec_diagonal, hr, mul_assoc, -Matrix.mulVec_mulVec] using ht
  funext i
  change (h.val *ᵥ RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z) i.castSucc / RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator h z =
    r⁻¹ * ((g.val *ᵥ RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector (r • z)) i.castSucc / RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator g (r • z))
  rw [hvec, hd]
  fin_cases i <;> simp [Matrix.mulVec_diagonal, mul_div_assoc, -Matrix.mulVec_mulVec]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RadiusChartConjugation.TestTransport
