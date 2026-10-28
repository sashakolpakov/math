import OAI.RepresentationTheory.Theta.Geometric.FlatAffineFunctionDescent

/-! # Regular Function Descent -/

namespace OAI.RepresentationTheory.Theta.Geometric.RegularFunctionDescent

noncomputable section

/-! Descent of compatible native regular functions, and its invariance
under actual scheme isomorphisms used by affine charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

def HasRegularFunctionDescent {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  ∀ r : Γ(X, ⊤),
    (∀ {Z : Scheme} (a b : Z ⟶ X), a ≫ f = b ≫ f → a.appTop r = b.appTop r) →
      ∃ s : Γ(Y, ⊤), f.appTop s = r

theorem flatEqualizerSpecMap_hasRegularFunctionDescent
    {A R P T : Type} [CommRing A] [CommRing R] [CommRing P] [CommRing T]
    [Algebra A R] [Algebra A P] [Algebra A T] [Module.Flat A T]
    (hi : Function.Injective (algebraMap A R)) (f g : R →ₐ[A] P)
    (he : Function.Exact (Algebra.linearMap A R) (f.toLinearMap - g.toLinearMap)) :
    HasRegularFunctionDescent (FlatAffineFunctionDescent.flatEqualizerSpecMap A R T) := by
  intro r hr
  exact (FlatAffineFunctionDescent.existsUnique_flatEqualizer_function_descent hi f g he r hr).exists

theorem HasRegularFunctionDescent.of_isomorphic
    {X Y X' Y' : Scheme} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (h : HasRegularFunctionDescent f') (eX : X' ≅ X) (eY : Y' ≅ Y)
    (he : eX.hom ≫ f = f' ≫ eY.hom) : HasRegularFunctionDescent f := by
  intro r hr
  have hr' : ∀ {Z : Scheme} (a b : Z ⟶ X'), a ≫ f' = b ≫ f' →
      a.appTop (eX.hom.appTop r) = b.appTop (eX.hom.appTop r) := by
    intro Z a b hab
    apply hr (a ≫ eX.hom) (b ≫ eX.hom)
    calc
      (a ≫ eX.hom) ≫ f = (a ≫ f') ≫ eY.hom := by rw [Category.assoc, he, Category.assoc]
      _ = (b ≫ f') ≫ eY.hom := congrArg (fun k => k ≫ eY.hom) hab
      _ = (b ≫ eX.hom) ≫ f := by simp only [Category.assoc, he]
  obtain ⟨s, hs⟩ := h (eX.hom.appTop r) hr'
  refine ⟨eY.inv.appTop s, ?_⟩
  have : IsIso eX.hom.appTop := inferInstanceAs (IsIso (Scheme.Γ.map eX.hom.op))
  apply (ConcreteCategory.bijective_of_isIso eX.hom.appTop).injective
  have he' : eX.hom ≫ f ≫ eY.inv = f' := by
    rw [← Category.assoc, he, Category.assoc, eY.hom_inv_id, Category.comp_id]
  have H := congrArg (fun k : X' ⟶ Y' => k.appTop s) he'
  exact H.trans hs

end

end OAI.RepresentationTheory.Theta.Geometric.RegularFunctionDescent
