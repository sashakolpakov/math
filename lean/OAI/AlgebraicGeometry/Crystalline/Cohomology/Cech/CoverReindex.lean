import OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve

/-! # Cover Reindex -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoverReindex.CechCoverReindex

noncomputable section

/-! Relabelling a cover across index universes preserves the actual Cech functor and total complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial _root_.AlgebraicTopology

universe u v w z a b

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type a} [Category.{b} A] [HasProducts.{w} A] [HasProducts.{z} A]
  {ι : Type w} {κ : Type z} (U : ι → C) (e : κ ≃ ι)

abbrev terms (P : Cᵒᵖ ⥤ A) (n : SimplexCategory) (t : Fin (n.len + 1) → ι) : A :=
  P.obj (op (∏ᶜ (U ∘ t)))

def cosimplicialMap (P : Cᵒᵖ ⥤ A) :
    (FormalCoproduct.cosimplicialObjectFunctor (NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U)).obj P ⟶
      (FormalCoproduct.cosimplicialObjectFunctor (NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (U ∘ e))).obj P where
  app n := Pi.lift (fun t => Pi.π (terms U P n) (e ∘ t))
  naturality n m f := by
    apply Pi.hom_ext
    intro t
    change ((Pi.lift (fun j => Pi.π (terms U P n) (j ∘ f.toOrderHom.toFun) ≫
      P.map (Pi.lift (fun k => Pi.π (U ∘ j) (f.toOrderHom.toFun k))).op)) ≫
        (Pi.lift (fun j => Pi.π (terms U P m) (e ∘ j)))) ≫
          Pi.π (terms (U ∘ e) P m) t =
      ((Pi.lift (fun j => Pi.π (terms U P n) (e ∘ j))) ≫
        (Pi.lift (fun j => Pi.π (terms (U ∘ e) P n) (j ∘ f.toOrderHom.toFun) ≫
          P.map (Pi.lift (fun k => Pi.π ((U ∘ e) ∘ j) (f.toOrderHom.toFun k))).op))) ≫
            Pi.π (terms (U ∘ e) P m) t
    simp only [Category.assoc]
    erw [Pi.lift_comp_π, Pi.lift_comp_π, Pi.lift_comp_π, Pi.lift_comp_π_assoc]
    rfl

theorem component_isIso (P : Cᵒᵖ ⥤ A) (n : SimplexCategory) :
    IsIso ((cosimplicialMap U e P).app n) := by
  let t : (Fin (n.len + 1) → κ) ≃ (Fin (n.len + 1) → ι) :=
    Equiv.piCongrRight (fun _ => e)
  let q : ∏ᶜ (terms (U ∘ e) P n) ≅ ∏ᶜ (terms U P n) :=
    Pi.whiskerEquiv (f := terms (U ∘ e) P n) (g := terms U P n) t (fun _ => Iso.refl _)
  have h : (cosimplicialMap U e P).app n = q.inv := by
    change (Pi.lift (fun j => Pi.π (terms U P n) (e ∘ j))) =
      CategoryTheory.Limits.Pi.map' t (fun j => 𝟙 (terms (U ∘ e) P n j))
    apply Pi.hom_ext
    intro j
    erw [Pi.lift_comp_π, Pi.map'_comp_π, Category.comp_id]
    rfl
  exact h.symm ▸ q.isIso_inv

def cosimplicialIso (P : Cᵒᵖ ⥤ A) :
    (FormalCoproduct.cosimplicialObjectFunctor (NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U)).obj P ≅
      (FormalCoproduct.cosimplicialObjectFunctor (NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (U ∘ e))).obj P := by
  let : ∀ n, IsIso ((cosimplicialMap U e P).app n) := component_isIso U e P
  let : IsIso (cosimplicialMap U e P) := NatIso.isIso_of_isIso_app _
  exact asIso (cosimplicialMap U e P)

variable [Preadditive A]

def complexIso (P : Cᵒᵖ ⥤ A) :
    (NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor U).obj P ≅
      (NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor (U ∘ e)).obj P :=
  (alternatingCofaceMapComplex A).mapIso (cosimplicialIso U e P)

theorem naturality {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) :
    (NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor U).map f ≫ (complexIso U e Q).hom =
      (complexIso U e P).hom ≫ (NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor (U ∘ e)).map f := by
  ext n : 1
  apply Pi.hom_ext
  intro t
  change ((CategoryTheory.Limits.Pi.map (fun j => f.app (op (∏ᶜ (U ∘ j))))) ≫
    (Pi.lift (fun j => Pi.π (terms U Q ⦋n⦌) (e ∘ j)))) ≫
      Pi.π (terms (U ∘ e) Q ⦋n⦌) t =
    ((Pi.lift (fun j => Pi.π (terms U P ⦋n⦌) (e ∘ j))) ≫
      (CategoryTheory.Limits.Pi.map (fun j => f.app (op (∏ᶜ ((U ∘ e) ∘ j)))))) ≫
        Pi.π (terms (U ∘ e) Q ⦋n⦌) t
  simp only [Category.assoc]
  erw [Pi.lift_comp_π, Pi.map_π, Pi.map_π, Pi.lift_comp_π_assoc]
  rfl

def functorIso : NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor (A := A) U ≅
    NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor (U ∘ e) :=
  NatIso.ofComponents (complexIso U e) (fun {_ _} f => CechCoverReindex.naturality U e f)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoverReindex.CechCoverReindex
