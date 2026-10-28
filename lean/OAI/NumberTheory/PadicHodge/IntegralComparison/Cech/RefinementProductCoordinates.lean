import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.Refinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBaseChange
import Mathlib.Algebra.Homology.QuasiIso

/-! # Refinement Product Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.RefinementProductCoordinates

noncomputable section

/-! Refinement commutes with the actual tuple-product comparison for
arbitrary small families. This also transports its quasi-isomorphism property. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v s t a b w
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type s} [Category.{t} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{w} A]
  (F : C ⥤ D) {ι κ : Type w} (U : ι → C) (V : κ → C)
  [∀ (n : ℕ) (z : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ z)) F]
  [∀ (n : ℕ) (z : Fin (n + 1) → κ), PreservesLimit (Discrete.functor (V ∘ z)) F]
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)

def mappedCover : FormalCoproduct.mk κ (F.obj ∘ V) ⟶
    FormalCoproduct.mk ι (F.obj ∘ U) where
  f := r.f
  φ j := F.map (r.φ j)

variable (P : Dᵒᵖ ⥤ A)

theorem naturality : GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r (F.op ⋙ P) ≫
    (GeometricComparison.NonemptyCech.ProductBaseChange.NonemptyCechProductBaseChange.complexIso F V P).hom =
      (GeometricComparison.NonemptyCech.ProductBaseChange.NonemptyCechProductBaseChange.complexIso F U P).hom ≫
        GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map (F.obj ∘ U) (F.obj ∘ V) (mappedCover F U V r) P := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply Pi.hom_ext
  intro z
  change Fin (n + 1) → κ at z
  let A₀ := fun z : Fin (n + 1) → ι => P.obj (op (F.obj (∏ᶜ (U ∘ z))))
  let A₁ := fun z : Fin (n + 1) → κ => P.obj (op (F.obj (∏ᶜ (V ∘ z))))
  let B₀ := fun z : Fin (n + 1) → ι => P.obj (op (∏ᶜ ((F.obj ∘ U) ∘ z)))
  let B₁ := fun z : Fin (n + 1) → κ => P.obj (op (∏ᶜ ((F.obj ∘ V) ∘ z)))
  let a : ∀ z : Fin (n + 1) → κ, A₀ (r.f ∘ z) ⟶ A₁ z := fun z =>
    P.map (F.map ((FormalCoproduct.powerMap r (Fin (n + 1))).φ z)).op
  let b : ∀ z : Fin (n + 1) → κ, B₀ (r.f ∘ z) ⟶ B₁ z := fun z =>
    P.map ((FormalCoproduct.powerMap (mappedCover F U V r) (Fin (n + 1))).φ z).op
  let e : ∀ z : Fin (n + 1) → ι, A₀ z ⟶ B₀ z := fun z =>
    P.map (PreservesProduct.iso F (U ∘ z)).inv.op
  let d : ∀ z : Fin (n + 1) → κ, A₁ z ⟶ B₁ z := fun z =>
    P.map (PreservesProduct.iso F (V ∘ z)).inv.op
  change (Pi.lift (fun z => Pi.π A₀ (r.f ∘ z) ≫ a z) ≫ Limits.Pi.map d) ≫ Pi.π B₁ z =
    (Limits.Pi.map e ≫ Pi.lift (fun z => Pi.π B₀ (r.f ∘ z) ≫ b z)) ≫ Pi.π B₁ z
  simp only [Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_comp_π_assoc, Limits.Pi.lift_comp_π,
    Limits.Pi.map_π_assoc]
  exact congrArg (fun x => Pi.π A₀ (r.f ∘ z) ≫ x)
    ((P.map_comp _ _).symm.trans
      ((congrArg P.map (Subsingleton.elim _ _)).trans (P.map_comp _ _)))

theorem quasiIso [QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r (F.op ⋙ P))] :
    QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map (F.obj ∘ U) (F.obj ∘ V)
      (mappedCover F U V r) P) := by
  apply (quasiIso_iff_comp_left (GeometricComparison.NonemptyCech.ProductBaseChange.NonemptyCechProductBaseChange.complexIso F U P).hom _).mp
  rw [← naturality]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.RefinementProductCoordinates
