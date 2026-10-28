import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.CechPullback

/-! # Pullback Projection -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.PullbackProjection.CechPullback

noncomputable section

/-! Projection formulas for actual Čech pullback on each intersection in a refined cover. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite Simplicial

theorem product_projection {A : Type*} [Category* A] {α β : Type}
    [HasProductsOfShape α A] [HasProductsOfShape β A]
    (X Y Z : α → A) (W : β → A) (b : ∀ i, X i ⟶ Y i) (e : ∀ i, Y i ≅ Z i)
    (r : β → α) (a : ∀ j, Z (r j) ⟶ W j) (t : β) :
    (Limits.Pi.map b ≫ (Pi.mapIso e).hom ≫ Pi.lift (fun j => Pi.π Z (r j) ≫ a j)) ≫ Pi.π W t =
      Pi.π X (r t) ≫ b (r t) ≫ (e (r t)).hom ≫ a t := by
  simp only [Category.assoc, Pi.lift_comp_π, Pi.mapIso_hom_π_assoc, Pi.map_π_assoc]

variable (R : Type) [CommRing R] {X Y : Scheme.{0}} (f : X ⟶ Y)
  {ι κ : Type} (U : ι → Y.Opens) (V : κ → X.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f ⁻¹ᵁ U (r i))

def intersectionHom (n : ℕ) (t : Fin (n + 1) → κ) :
    (∏ᶜ (V ∘ t)) ⟶ f ⁻¹ᵁ (∏ᶜ (U ∘ (r ∘ t))) :=
  ((FormalCoproduct.cechFunctor.map (Refinement.CechRefinement.coverMap X (fun i => f ⁻¹ᵁ U i) V r hr)).app
    (op ⦋n⦌)).φ t ≫ (PreservesProduct.iso (Image.CechImage.preimage f) (U ∘ (r ∘ t))).inv

theorem map_f_π {P : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R Y} {Q : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X}
    (b : P ⟶ (Image.CechImage.functor R f).obj Q) (n : ℕ) (t : Fin (n + 1) → κ) :
    (CechPullback.map R f U V r hr b).f n ≫ Pi.π (fun t : Fin (n + 1) → κ => Q.obj (op (∏ᶜ (V ∘ t)))) t =
      Pi.π (fun s : Fin (n + 1) → ι => P.obj (op (∏ᶜ (U ∘ s)))) (r ∘ t) ≫
        b.app (op (∏ᶜ (U ∘ (r ∘ t)))) ≫ Q.map (intersectionHom f U V r hr n t).op := by
  let a : FormalCoproduct.mk (Fin (n + 1) → κ) (fun t => ∏ᶜ (V ∘ t)) ⟶
      FormalCoproduct.mk (Fin (n + 1) → ι) (fun t => ∏ᶜ (fun i => f ⁻¹ᵁ U (t i))) :=
    (FormalCoproduct.cechFunctor.map (Refinement.CechRefinement.coverMap X (fun i => f ⁻¹ᵁ U i) V r hr)).app (op ⦋n⦌)
  let P₀ := fun s : Fin (n + 1) → ι => P.obj (op (∏ᶜ (U ∘ s)))
  let M₀ := fun s : Fin (n + 1) → ι => Q.obj (op (f ⁻¹ᵁ (∏ᶜ (U ∘ s))))
  let N₀ := fun s : Fin (n + 1) → ι => Q.obj (op (∏ᶜ (fun i => f ⁻¹ᵁ U (s i))))
  let T₀ := fun s : Fin (n + 1) → κ => Q.obj (op (∏ᶜ (V ∘ s)))
  let b₀ : ∀ s, P₀ s ⟶ M₀ s := fun s => b.app (op (∏ᶜ (U ∘ s)))
  let e : ∀ s, M₀ s ≅ N₀ s := fun s =>
    Q.mapIso (PreservesProduct.iso (Image.CechImage.preimage f) (U ∘ s)).symm.op
  let a₀ : ∀ s, N₀ (r ∘ s) ⟶ T₀ s := fun s => Q.map (a.φ s).op
  have hx := product_projection P₀ M₀ N₀ T₀ b₀ e (fun s => r ∘ s) a₀ t
  have hc : (e (r ∘ t)).hom ≫ a₀ t = Q.map (intersectionHom f U V r hr n t).op :=
    (Q.map_comp (PreservesProduct.iso (Image.CechImage.preimage f) (U ∘ (r ∘ t))).symm.op.hom
      (a.φ t).op).symm
  exact hx.trans (congrArg (fun k => Pi.π P₀ (r ∘ t) ≫ b₀ (r ∘ t) ≫ k) hc)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.PullbackProjection.CechPullback
