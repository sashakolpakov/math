import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.AffineTargetNilLift

/-! # Affine Open Nil Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.AffineOpenNilLift

noncomputable section

/-! Unique nilpotent lifting into an affine etale chart over an affine
open of an arbitrary base. Surjectivity of the reduction supplies the
required factorization through the base open. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X U Y T T₀ : Scheme.{u}} [IsAffine U] [IsAffine Y]
  (f : Y ⟶ U) [Etale f] (j : U ⟶ X) [IsOpenImmersion j]
  (i : T₀ ⟶ T) [IsClosedImmersion i] [Surjective i]
  (hi : IsNilpotent i.ker) (a : T₀ ⟶ Y) (b : T ⟶ X)
  (hab : a ≫ f ≫ j = i ≫ b)

include hab in
omit [IsAffine U] [IsAffine Y] [Etale f] [IsOpenImmersion j] [IsClosedImmersion i] in
theorem base_range : Set.range b ⊆ Set.range j := by
  rintro _ ⟨t, rfl⟩
  obtain ⟨t₀, rfl⟩ := i.surjective t
  refine ⟨f (a t₀), ?_⟩
  exact congrArg (fun g : T₀ ⟶ X => g t₀) hab

def base : T ⟶ U := IsOpenImmersion.lift j b (base_range f j i a b hab)

omit [IsAffine U] [IsAffine Y] [Etale f] [IsClosedImmersion i] in
theorem base_reduction : i ≫ base f j i a b hab = a ≫ f := by
  apply (cancel_mono j).mp
  rw [Category.assoc, base, IsOpenImmersion.lift_fac]
  simpa only [Category.assoc] using hab.symm

include hi hab in
theorem existsUnique_lift : ∃! l : T ⟶ Y, i ≫ l = a ∧ l ≫ f ≫ j = b := by
  obtain ⟨l, hl, hu⟩ := AffineTargetNilLift.existsUnique_lift f i hi a
    (base f j i a b hab) (base_reduction f j i a b hab).symm
  refine ⟨l, ⟨hl.1, ?_⟩, ?_⟩
  · rw [← Category.assoc, hl.2, base, IsOpenImmersion.lift_fac]
  · intro m hm
    apply hu m
    refine ⟨hm.1, ?_⟩
    apply (cancel_mono j).mp
    rw [Category.assoc, hm.2, base, IsOpenImmersion.lift_fac]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.AffineOpenNilLift
