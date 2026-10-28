import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBaseChangeNaturality

/-! # Product Composition -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductComposition.NonemptyCechProductComposition

noncomputable section

/-! The original nonempty Cech product comparison respects
successive indexing functors into thin categories of opens. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v s t d e a b
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type s} [Category.{t} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {E : Type d} [Category.{e} E] [Quiver.IsThin E] [HasBinaryProducts E]
  {A : Type a} [Category.{b} A] [Preadditive A] [HasProducts.{0} A]
  (F : C ⥤ D) (G : D ⥤ E) {ι : Type} (U : ι → C)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor ((F.obj ∘ U) ∘ t)) G]
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) (F ⋙ G)]
  (P : Eᵒᵖ ⥤ A)

theorem composition : (ProductBaseChange.NonemptyCechProductBaseChange.complexIso F U (G.op ⋙ P)).hom ≫
    (ProductBaseChange.NonemptyCechProductBaseChange.complexIso G (F.obj ∘ U) P).hom =
      (ProductBaseChange.NonemptyCechProductBaseChange.complexIso (F ⋙ G) U P).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  change Limits.Pi.map (fun t : Fin (n + 1) → ι =>
      P.map (G.map (PreservesProduct.iso F (U ∘ t)).inv).op) ≫
    Limits.Pi.map (fun t : Fin (n + 1) → ι =>
      P.map (PreservesProduct.iso G ((F.obj ∘ U) ∘ t)).inv.op) =
    Limits.Pi.map (fun t : Fin (n + 1) → ι =>
      P.map (PreservesProduct.iso (F ⋙ G) (U ∘ t)).inv.op)
  erw [Limits.Pi.map_comp_map]
  congr 1
  funext t
  exact (P.map_comp _ _).symm.trans (congrArg P.map (Subsingleton.elim _ _))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductComposition.NonemptyCechProductComposition
