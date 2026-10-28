import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Section Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.SectionRestriction

noncomputable section

/-! A section of a scheme morphism restricts canonically to every open subset of its base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}}

def familySectionRestrict (p : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 _) (U : S.Opens) :
    U.toScheme ⟶ (p ⁻¹ᵁ U).toScheme :=
  (isPullback_morphismRestrict p U).flip.lift (U.ι ≫ σ) (𝟙 U.toScheme)
    (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])

theorem familySectionRestrict_projection (p : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 _) (U : S.Opens) :
    familySectionRestrict p σ hσ U ≫ (p ∣_ U) = 𝟙 U.toScheme :=
  (isPullback_morphismRestrict p U).flip.lift_snd _ _ _

theorem familySectionRestrict_inclusion (p : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 _) (U : S.Opens) :
    familySectionRestrict p σ hσ U ≫ (p ⁻¹ᵁ U).ι = U.ι ≫ σ :=
  (isPullback_morphismRestrict p U).flip.lift_fst _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.SectionRestriction
