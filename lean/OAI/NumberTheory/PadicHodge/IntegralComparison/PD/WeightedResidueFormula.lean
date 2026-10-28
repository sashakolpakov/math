import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicResidueFormula

/-! # Weighted Residue Formula -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.WeightedResidueFormula.LogarithmicForms

noncomputable section

/-! A coefficient in the base ring multiplies the literal numerator
of the logarithmic PD residue. -/

open scoped BigOperators

universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (δ : DividedPowers I)

theorem scalar_logarithmicWedge_symbol (n : ℕ) (v : Fin n → Aˣ) (r : R) :
    r • LogarithmicWedges.Forms.logarithmicWedge R A I δ n v =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ
        (algebraMap R A r * (↑((∏ i, v i)⁻¹) : A)) (fun i => (v i : A)) := by
  rw [LogarithmicResidueFormula.Forms.logarithmicWedge_reciprocal_product,
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol_smul_one R A I δ (↑((∏ i, v i)⁻¹) : A),
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol_smul_one R A I δ (algebraMap R A r * (↑((∏ i, v i)⁻¹) : A))]
  rw [← IsScalarTower.algebraMap_smul A r, smul_smul]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.WeightedResidueFormula.LogarithmicForms
