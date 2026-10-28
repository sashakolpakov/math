import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.ObjectwiseResolution

/-! # Augmentation Formula -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.AugmentationFormula.KoszulAugmentationFormula

noncomputable section

/-! # The original objectwise Koszul augmentation on degree-zero sections -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u v w

variable (R σ : Type u) [CommRing R] [Fintype σ]
  {C : Type v} [Category.{w} C] (F G : C ⥤ ModuleCat.{u} R)
  (D : σ → (F ⟶ F)) (S : ∀ t : C, σ → Module.End R (F.obj t))

local notation "d" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Functor.KoszulFunctor.derivatives R σ F D
local notation "s" => S

variable (hD : ∀ (t : C) (i j : σ),
    Function.Commute (Functor.KoszulFunctor.derivatives R σ F D t i) (Functor.KoszulFunctor.derivatives R σ F D t j))
  (hright : ∀ (t : C) (i : σ) (a : F.obj t),
    Functor.KoszulFunctor.derivatives R σ F D t i (S t i a) = a)
  (hcommS : ∀ (t : C) (i j : σ), j ≠ i → ∀ a : F.obj t,
    Functor.KoszulFunctor.derivatives R σ F D t j (S t i a) =
      S t i (Functor.KoszulFunctor.derivatives R σ F D t j a))
  (l : List σ) (hl : ∀ i, i ∈ l) (c : G ⟶ F) (r : ∀ t : C, F.obj t →ₗ[R] G.obj t)
  (hrc : ∀ t, (r t).comp (c.app t).hom = LinearMap.id)
  (hc : ∀ (t : C) (i : σ) (a : G.obj t), Functor.KoszulFunctor.derivatives R σ F D t i ((c.app t).hom a) = 0)
  (hprojection : ∀ t, SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient R σ (F.obj t)
    (Functor.KoszulFunctor.derivatives R σ F D t) (S t) l =
    (c.app t).hom.comp (r t))

theorem zero (t : C) (x : G.obj t) :
    (((ObjectwiseResolution.KoszulObjectwiseResolution.augmentation R σ F G D S hD hright hcommS l hl c r hrc hc hprojection).f 0).app t).hom x =
      (c.app t).hom x ⊗ₜ[R] (exteriorPower.zeroEquiv R (σ →₀ R)).symm 1 := by
  change (((ObjectwiseResolution.KoszulObjectwiseResolution.homotopyEquiv R σ F G D S hD hright hcommS l hl c r hrc hc hprojection t).hom).f 0).hom x = _
  rw [ObjectwiseResolution.KoszulObjectwiseResolution.augmentation_zero]
  exact TensorDegree.TensorDegreeZero.equiv_symm R σ (F.obj t) ((c.app t).hom x)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.AugmentationFormula.KoszulAugmentationFormula
