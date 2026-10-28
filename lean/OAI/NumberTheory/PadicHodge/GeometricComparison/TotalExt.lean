import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.ExtVanishing
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalDiagonal
import OAI.AlgebraicGeometry.Comparison.Betti.TotalExists

/-! # Total Ext -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.TotalExt.TotalExtVanishing

noncomputable section

/-! Termwise coefficient Ext vanishing passes to first-quadrant total complexes through finite diagonals. -/

open _root_.CategoryTheory Abelian Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  (A : C) (B : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) [B.HasTotal (.up ℕ)]

theorem subsingleton (n q : ℕ)
    (hB : ∀ a b, Subsingleton (Ext.{w} A ((B.X a).X b) q)) :
    Subsingleton (Ext.{w} A ((B.total (.up ℕ)).X n) q) := by
  have : Finite ((ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) ⁻¹' {n}) := by
    change Finite {p : ℕ × ℕ // p.1 + p.2 = n}
    exact AlgebraicGeometry.Comparison.Betti.Finite.TotalDiagonal.finiteTotalDiagonal n
  exact GeometricComparison.Finite.ExtVanishing.FiniteExtVanishing.coproduct A
    (B.toGradedObject.mapObjFun (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n) q
    (fun p => hB p.val.1 p.val.2)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.TotalExt.TotalExtVanishing
