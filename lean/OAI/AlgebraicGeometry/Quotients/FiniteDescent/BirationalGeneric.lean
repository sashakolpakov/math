import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GenericLift

/-! # Birational Generic -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.BirationalGeneric.Construction.BirationalGenericLift

noncomputable section

/-! An isomorphism above a dense open gives a dense lift of the generic point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem dominant_of_comp_open {X Y Z : Scheme.{u}} (g : Y ⟶ X) (i : X ⟶ Z)
    [IsOpenImmersion i] [IsDominant (g ≫ i)] : IsDominant g := by
  constructor
  apply i.isOpenEmbedding.isEmbedding.isInducing.dense_iff.mpr
  intro x
  rw [← Set.range_comp]
  exact (g ≫ i).denseRange (i x)

theorem dominant_generic (Y : Scheme.{u}) [IsIntegral Y] :
    IsDominant (Y.fromSpecStalk (genericPoint Y)) := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← (genericPoint_spec Y).def]
  apply closure_mono
  rw [Set.singleton_subset_iff]
  exact ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩

theorem dominant_generic_open {Y : Scheme.{u}} [IsIntegral Y]
    (U : Y.Opens) [Nonempty U] :
    IsDominant (U.fromSpecStalkOfMem (genericPoint Y) (GenericLift.Construction.GenericLiftRestriction.generic_mem U)) := by
  have : IsDominant (U.fromSpecStalkOfMem (genericPoint Y)
      (GenericLift.Construction.GenericLiftRestriction.generic_mem U) ≫ U.ι) := by
    rw [Scheme.Opens.fromSpecStalkOfMem_ι]
    exact dominant_generic Y
  exact dominant_of_comp_open _ U.ι

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : X ⟶ Y) (U : Y.Opens) [Nonempty U] [IsIso (f ∣_ U)]

def lift : Spec Y.functionField ⟶ X :=
  U.fromSpecStalkOfMem (genericPoint Y) (GenericLift.Construction.GenericLiftRestriction.generic_mem U) ≫
    inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι

omit [IsIntegral X] in
theorem lift_comp : lift f U ≫ f = Y.fromSpecStalk (genericPoint Y) := by
  dsimp only [lift]
  rw [Category.assoc, Category.assoc, ← morphismRestrict_ι,
    IsIso.inv_hom_id_assoc, Scheme.Opens.fromSpecStalkOfMem_ι]

theorem isDominant_lift : IsDominant (lift f U) := by
  have : Nonempty (f ⁻¹ᵁ U).toScheme :=
    ⟨inv (f ∣_ U) (Classical.choice ‹Nonempty U›)⟩
  have : IsDominant (f ⁻¹ᵁ U).ι :=
    AlgebraicGeometry.Opens.isDominant_ι
      ((f ⁻¹ᵁ U).isOpen.dense (by simpa using ‹Nonempty (f ⁻¹ᵁ U).toScheme›))
  have := dominant_generic_open U
  dsimp only [lift]
  infer_instance

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.BirationalGeneric.Construction.BirationalGenericLift
