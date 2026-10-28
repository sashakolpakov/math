import OAI.AlgebraicGeometry.Comparison.Betti.Godement.TotalQuasiIso
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.TotalNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.FlasqueFiniteCoproduct

/-! # Total Flasque -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.TotalFlasque

noncomputable section

/-! Every term of the original nonnegative Godement total is flasque. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {X : TopCat.{0}} (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X) ℕ)

theorem godementTotal_isFlasque (n : ℕ) : TopCat.Sheaf.IsFlasque ((Bicomplex.godementTotal K).X n) := by
  let B := Bicomplex.godementBicomplex X K
  have hfin : Finite ((ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) ⁻¹' {n}) :=
    Betti.Finite.TotalDiagonal.finiteTotalDiagonal n
  change TopCat.Sheaf.IsFlasque
    (∐ B.toGradedObject.mapObjFun (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n)
  apply FlasqueFiniteCoproduct.finiteCoproduct_flasque
  intro p
  exact Resolution.godementComplex_isFlasque X (K.X p.val.1) p.val.2

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.TotalFlasque
