import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DominantOpen
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Open Section -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.OpenSection.ProperOpenSection

noncomputable section

/-! A dense open section of a proper morphism fills the whole inverse image of its base open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem isIso_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (U : Y.Opens) (j : U.toScheme ⟶ X) [IsOpenImmersion j] [IsDominant j]
    (hj : j ≫ f = U.ι) : IsIso (f ∣_ U) := by
  have hr : Set.range j ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rintro _ ⟨y, rfl⟩
    refine ⟨⟨j y, ?_⟩, rfl⟩
    change f (j y) ∈ U
    rw [← Scheme.Hom.comp_apply, hj]
    exact y.2
  let b := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι j hr
  have hb : b ≫ f ∣_ U = 𝟙 U.toScheme := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc,
      IsOpenImmersion.lift_fac, hj, Category.id_comp]
  have : IsDominant b := DominantOpen.DominantOpenLift.dominant_lift _ _ hr
  have : IsOpenImmersion b := inferInstance
  have : IsProper (b ≫ f ∣_ U) := by rw [hb]; infer_instance
  have : IsProper b := IsProper.of_comp b (f ∣_ U)
  have : Surjective b := inferInstance
  have : Epi b.base := ConcreteCategory.epi_of_surjective _ b.surjective
  have : IsIso b := IsOpenImmersion.isIso b
  have : IsIso (b ≫ f ∣_ U) := by rw [hb]; infer_instance
  exact IsIso.of_isIso_comp_left b (f ∣_ U)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.OpenSection.ProperOpenSection
