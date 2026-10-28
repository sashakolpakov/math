import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicWedges

/-! # Logarithmic Residue Formula -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicResidueFormula.Forms

noncomputable section

/-! The native logarithmic residue is literally the coordinate top
form divided by the product of its coordinates. No factorial or
additional sign enters the Koszul-to-Čech normalization. -/
open scoped BigOperators
universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (δ : DividedPowers I)

theorem logarithmicWedge_symbol (n : ℕ) (v : Fin n → Aˣ) :
    LogarithmicWedges.Forms.logarithmicWedge R A I δ n v =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ (∏ i, (↑(v i)⁻¹ : A)) (fun i => (v i : A)) := by
  induction n with
  | zero =>
      simp only [LogarithmicWedges.Forms.logarithmicWedge, DeRhamWedgeAlgebra.unitForm, Finset.univ_eq_empty, Finset.prod_empty]
      congr 1
      ext i
      exact i.elim0
  | succ n ih =>
      rw [LogarithmicWedges.Forms.logarithmicWedge, ih, LogarithmicForms.dlog_symbol, DeRhamWedge.wedge_symbol, Fin.prod_univ_castSucc]
      congr 1
      rw [Fin.append_right_eq_snoc]
      exact Fin.snoc_init_self (fun i => (v i : A))

theorem logarithmicWedge_reciprocal_product (n : ℕ) (v : Fin n → Aˣ) :
    LogarithmicWedges.Forms.logarithmicWedge R A I δ n v =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ (↑((∏ i, v i)⁻¹) : A) (fun i => (v i : A)) := by
  rw [logarithmicWedge_symbol]
  congr 1
  rw [← Finset.prod_inv_distrib, Units.coe_prod]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicResidueFormula.Forms
