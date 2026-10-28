import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RestrictedAwaySame

/-! # Restricted Insert -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RestrictedInsert.Approximation

noncomputable section

section

/-! Insert the identity at the omitted place. This continuous section of
the actual restricted product leaves every away coordinate unchanged. -/

open scoped Classical RestrictedProduct
open Filter

theorem cofinite_away_lift {I : Type*} (v : I) {p : I → Prop}
    (hv : p v) (h : ∀ᶠ w : {w : I // w ≠ v} in cofinite, p w.val) :
    ∀ᶠ w : I in cofinite, p w := by
  rw [eventually_cofinite] at h ⊢
  refine (h.image Subtype.val).subset ?_
  intro w hw
  have hwv : w ≠ v := fun he => hw (he.symm ▸ hv)
  exact ⟨⟨w, hwv⟩, hw, rfl⟩

variable {I : Type*} {G : I → Type*} [∀ i, Group (G i)]
  (K : ∀ i, Subgroup (G i)) (v : I)

def insertIdentityFunction (g : ∀ w : {w : I // w ≠ v}, G w.val) (w : I) : G w :=
  if hw : w = v then 1 else g ⟨w, hw⟩

def restrictedInsertPlace : RestrictedAwaySame.Approximation.RestrictedAway K v →* RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K where
  toFun g := ⟨insertIdentityFunction v g, by
    apply cofinite_away_lift v (by simp [insertIdentityFunction])
    filter_upwards [g.property] with w hw
    change g w ∈ K w.val at hw
    change (if he : w.val = v then 1 else g ⟨w.val, he⟩) ∈ K w.val
    rw [dite_eq_right w.property]
    exact hw⟩
  map_one' := by
    apply RestrictedProduct.ext
    intro w
    change insertIdentityFunction v (1 : RestrictedAwaySame.Approximation.RestrictedAway K v) w = 1
    by_cases hw : w = v <;> simp [insertIdentityFunction, hw]
  map_mul' g h := by
    apply RestrictedProduct.ext
    intro w
    change insertIdentityFunction v (g * h) w =
      insertIdentityFunction v g w * insertIdentityFunction v h w
    by_cases hw : w = v <;> simp [insertIdentityFunction, hw]

theorem restrictedInsertPlace_same (g : RestrictedAwaySame.Approximation.RestrictedAway K v) :
    restrictedInsertPlace K v g v = 1 := by
  change insertIdentityFunction v g v = 1
  simp [insertIdentityFunction]

theorem restrictedInsertPlace_other (g : RestrictedAwaySame.Approximation.RestrictedAway K v) (w : I) (hw : w ≠ v) :
    restrictedInsertPlace K v g w = g ⟨w, hw⟩ := by
  change insertIdentityFunction v g w = g ⟨w, hw⟩
  simp only [insertIdentityFunction, dite_eq_right hw]

theorem restrictedForgetInsert (g : RestrictedAwaySame.Approximation.RestrictedAway K v) :
    RestrictedAwaySame.Approximation.restrictedForgetPlace K v (restrictedInsertPlace K v g) = g := by
  apply RestrictedProduct.ext
  intro w
  exact restrictedInsertPlace_other K v g w.val w.property

theorem restrictedInsertForget (g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K) :
    RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K v (g v) * restrictedInsertPlace K v (RestrictedAwaySame.Approximation.restrictedForgetPlace K v g) = g := by
  apply RestrictedProduct.ext
  intro w
  by_cases hw : w = v
  · subst w
    change RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K v (g v) v * restrictedInsertPlace K v (RestrictedAwaySame.Approximation.restrictedForgetPlace K v g) v = g v
    rw [RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace_same, restrictedInsertPlace_same, mul_one]
  · change RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K v (g v) w * restrictedInsertPlace K v (RestrictedAwaySame.Approximation.restrictedForgetPlace K v g) w = g w
    rw [RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace_other K hw, restrictedInsertPlace_other K v _ w hw, one_mul]
    rfl

variable [∀ i, TopologicalSpace (G i)]

theorem restrictedInsertPlace_continuous : Continuous (restrictedInsertPlace K v) := by
  rw [RestrictedProduct.continuous_dom]
  intro S hS
  let T : Set I := {w | ∀ hw : w ≠ v, (⟨w, hw⟩ : {w : I // w ≠ v}) ∈ S}
  have hT : cofinite ≤ principal T := by
    rw [le_principal_iff]
    apply cofinite_away_lift v (by simp)
    filter_upwards [le_principal_iff.mp hS] with w hw
    exact fun _ => hw
  let f : RestrictedProduct (fun w : {w : I // w ≠ v} => G w.val)
      (fun w => (K w.val : Set (G w.val))) (principal S) →
      RestrictedProduct G (fun w => (K w : Set (G w))) (principal T) := fun g =>
    ⟨insertIdentityFunction v g, by
      rw [eventually_principal]
      intro w hw
      by_cases he : w = v
      · simp [insertIdentityFunction, he]
      · change (if h : w = v then 1 else g ⟨w, h⟩) ∈ K w
        rw [dite_eq_right he]
        exact (eventually_principal.mp g.property) ⟨w, he⟩ (hw he)⟩
  have hf : Continuous f := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    apply continuous_pi
    intro w
    change Continuous (fun g : RestrictedProduct (fun w : {w : I // w ≠ v} => G w.val)
      (fun w => (K w.val : Set (G w.val))) (principal S) => insertIdentityFunction v g w)
    by_cases hw : w = v
    · simp only [insertIdentityFunction, dite_eq_left hw]
      exact continuous_const
    · simp only [insertIdentityFunction, dite_eq_right hw]
      exact RestrictedProduct.continuous_eval (R := fun w : {w : I // w ≠ v} => G w.val)
        (A := fun w => (K w.val : Set (G w.val))) (𝓕 := principal S) ⟨w, hw⟩
  exact (RestrictedProduct.continuous_inclusion hT).comp hf

def restrictedInsertPlaceContinuous : RestrictedAwaySame.Approximation.RestrictedAway K v →ₜ* RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K :=
  ⟨restrictedInsertPlace K v, restrictedInsertPlace_continuous K v⟩

end

/-! Open active subgroups compatible with a prescribed restricted-product level. -/

variable {I : Type*} {G : I → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  (K : ∀ i, Subgroup (G i)) (v : I)
  {A : Type*} [Group A] [TopologicalSpace A]
  (L : OpenSubgroup (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K)) (J : OpenSubgroup A) (j : A →ₜ* G v)

def restrictedActiveLevel : OpenSubgroup A :=
  J ⊓ L.comap ((RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlaceContinuous K v).comp j).toMonoidHom
    ((RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlaceContinuous K v).comp j).continuous

theorem restrictedActiveLevel_le : restrictedActiveLevel K v L J j ≤ J := inf_le_left

theorem restrictedActiveLevel_mem (g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K) (a : A)
    (hj : j a = g v) (ha : a ∈ restrictedActiveLevel K v L J j)
    (hg : restrictedInsertPlace K v (RestrictedAwaySame.Approximation.restrictedForgetPlace K v g) ∈ L) : g ∈ L := by
  have h : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K v (j a) ∈ L := ha.2
  rw [hj] at h
  have hm := L.mul_mem h hg
  rwa [restrictedInsertForget] at hm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RestrictedInsert.Approximation
