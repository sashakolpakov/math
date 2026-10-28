import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange

/-! # Termwise Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TermwiseIso.CechTermwiseIso

noncomputable section

/-! A map of actual Čech complexes is invertible when it is invertible on every intersection coefficient. -/

open _root_.CategoryTheory Limits Opposite Simplicial

universe u v w z t

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
  [Preadditive D] [HasProducts.{t} D]
  (E : SimplicialObject (FormalCoproduct.{t} C)) {P Q : Cᵒᵖ ⥤ D} (f : P ⟶ Q)

theorem isIso (h : ∀ n : ℕ, ∀ i : (E.obj (op ⦋n⦌)).I,
    IsIso (f.app (op ((E.obj (op ⦋n⦌)).obj i)))) :
    IsIso ((FormalCoproduct.cochainComplexFunctor E).map f) := by
  have (n : ℕ) : IsIso (((FormalCoproduct.cochainComplexFunctor E).map f).f n) := by
    have (i : (E.obj (op ⦋n⦌)).I) : IsIso (f.app (op ((E.obj (op ⦋n⦌)).obj i))) := h n i
    change IsIso (Limits.Pi.map (fun i : (E.obj (op ⦋n⦌)).I => f.app (op ((E.obj (op ⦋n⦌)).obj i))))
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TermwiseIso.CechTermwiseIso
