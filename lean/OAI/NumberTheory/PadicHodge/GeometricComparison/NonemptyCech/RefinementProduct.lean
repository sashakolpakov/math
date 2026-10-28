import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.Refinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBaseChangeNaturality

/-! # Refinement Product -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.RefinementProduct.NonemptyCechRefinementProduct

noncomputable section

/-! Refinement of the original Cech cover commutes with the
actual tuple-product isomorphism into a thin category of opens. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v s t a b
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type s} [Category.{t} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {A : Type a} [Category.{b} A] [Preadditive A] [HasProducts.{0} A]
  (F : C ⥤ D) {ι κ : Type} (U : ι → C) (V : κ → C)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  [∀ (n : ℕ) (t : Fin (n + 1) → κ), PreservesLimit (Discrete.functor (V ∘ t)) F]
  (r : FormalCoproduct.mk ι U ⟶ FormalCoproduct.mk κ V)

def mappedCover : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ (F.obj ∘ V) where
  f := r.f
  φ j := F.map (r.φ j)

variable (P : Dᵒᵖ ⥤ A)

theorem naturality : Refinement.NonemptyCechRefinement.map V U r (F.op ⋙ P) ≫
    (ProductBaseChange.NonemptyCechProductBaseChange.complexIso F U P).hom =
      (ProductBaseChange.NonemptyCechProductBaseChange.complexIso F V P).hom ≫
        Refinement.NonemptyCechRefinement.map (F.obj ∘ V) (F.obj ∘ U) (mappedCover F U V r) P := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply Pi.hom_ext
  intro t
  change Fin (n + 1) → ι at t
  let A₀ := fun s : Fin (n + 1) → κ => P.obj (op (F.obj (∏ᶜ (V ∘ s))))
  let A₁ := fun s : Fin (n + 1) → ι => P.obj (op (F.obj (∏ᶜ (U ∘ s))))
  let B₀ := fun s : Fin (n + 1) → κ => P.obj (op (∏ᶜ ((F.obj ∘ V) ∘ s)))
  let B₁ := fun s : Fin (n + 1) → ι => P.obj (op (∏ᶜ ((F.obj ∘ U) ∘ s)))
  let a : ∀ s : Fin (n + 1) → ι, A₀ (r.f ∘ s) ⟶ A₁ s := fun s => P.map (F.map ((FormalCoproduct.powerMap r (Fin (n + 1))).φ s)).op
  let b : ∀ s : Fin (n + 1) → ι, B₀ (r.f ∘ s) ⟶ B₁ s := fun s =>
    P.map ((FormalCoproduct.powerMap (mappedCover F U V r) (Fin (n + 1))).φ s).op
  let e : ∀ s : Fin (n + 1) → κ, A₀ s ⟶ B₀ s := fun s => P.map (PreservesProduct.iso F (V ∘ s)).inv.op
  let d : ∀ s : Fin (n + 1) → ι, A₁ s ⟶ B₁ s := fun s => P.map (PreservesProduct.iso F (U ∘ s)).inv.op
  change (Pi.lift (fun s => Pi.π A₀ (r.f ∘ s) ≫ a s) ≫ Limits.Pi.map d) ≫ Pi.π B₁ t =
    (Limits.Pi.map e ≫ Pi.lift (fun s => Pi.π B₀ (r.f ∘ s) ≫ b s)) ≫ Pi.π B₁ t
  simp only [Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_comp_π_assoc, Limits.Pi.lift_comp_π, Limits.Pi.map_π_assoc]
  exact congrArg (fun x => Pi.π A₀ (r.f ∘ t) ≫ x)
    ((P.map_comp _ _).symm.trans ((congrArg P.map (Subsingleton.elim _ _)).trans (P.map_comp _ _)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.RefinementProduct.NonemptyCechRefinementProduct
