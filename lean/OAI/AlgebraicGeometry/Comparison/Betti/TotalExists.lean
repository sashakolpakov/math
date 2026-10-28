import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalDiagonal

/-! # Total Exists -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.TotalExists

/-! Supply total-complex existence from the ambient category's coproducts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteCoproducts C]

theorem hasTotal_of_finiteCoproducts (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) :
    K.HasTotal (.up ℕ) := by
  intro n
  have : Finite ((ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) ⁻¹' {n}) := by
    change Finite {p : ℕ × ℕ // p.1 + p.2 = n}
    exact Betti.Finite.TotalDiagonal.finiteTotalDiagonal n
  infer_instance

end OAI.AlgebraicGeometry.Comparison.Betti.TotalExists
