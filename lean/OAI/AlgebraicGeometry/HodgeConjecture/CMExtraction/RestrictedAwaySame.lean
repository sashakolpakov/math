import OAI.RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits

/-! # Restricted Away Same -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RestrictedAwaySame.Approximation

noncomputable section

/-! Remove one specified local factor from the actual restricted product.
The forgetful homomorphism and the remaining local inclusions are continuous. -/

open scoped Classical RestrictedProduct
open Filter OAI.RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction

variable {I : Type*} {G : I → Type*} [∀ i, Group (G i)]
  (K : ∀ i, Subgroup (G i)) (v : I)

abbrev RestrictedAway := RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup (fun w : {w : I // w ≠ v} => K w.val)

def restrictedForgetPlace : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K →* RestrictedAway K v :=
  RestrictedProduct.mapAlongMonoidHom G (fun w : {w : I // w ≠ v} => G w.val)
    Subtype.val Subtype.val_injective.tendsto_cofinite
    (fun _ => MonoidHom.id _) (Eventually.of_forall fun _ _ hx => hx)

theorem restrictedForgetPlace_apply (g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K) (w : {w : I // w ≠ v}) :
    restrictedForgetPlace K v g w = g w.val := rfl

theorem restrictedForgetPlace_include_same (g : G v) :
    restrictedForgetPlace K v (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K v g) = 1 := by
  apply RestrictedProduct.ext
  intro w
  exact RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace_other K w.property g

variable [∀ i, TopologicalSpace (G i)]

theorem restrictedForgetPlace_continuous : Continuous (restrictedForgetPlace K v) :=
  RestrictedProduct.mapAlong_continuous G (fun w : {w : I // w ≠ v} => G w.val)
    (A₁ := fun i => (K i : Set (G i)))
    (A₂ := fun w => (K w.val : Set (G w.val)))
    Subtype.val Subtype.val_injective.tendsto_cofinite (fun _ g => g)
    (Eventually.of_forall fun _ _ hx => hx) (fun _ => continuous_id)

def restrictedForgetPlaceContinuous : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K →ₜ* RestrictedAway K v :=
  ⟨restrictedForgetPlace K v, restrictedForgetPlace_continuous K v⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RestrictedAwaySame.Approximation
