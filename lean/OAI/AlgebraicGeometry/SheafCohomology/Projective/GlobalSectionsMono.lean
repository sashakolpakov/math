import OAI.AlgebraicGeometry.SheafCohomology.Projective.HomSectionEquivEvaluation

/-! # Global Sections Mono -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsMono

noncomputable section

/-! Global sections preserve injectivity of morphisms of actual module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem unitHomTopSectionsEquiv_comp {X : Scheme.{u}} {M N : X.Modules}
    (f : Invertible.Scheme.Modules.unitObj X ⟶ M) (g : M ⟶ N) :
    UnitHomTopSections.unitHomTopSectionsEquiv N (f ≫ g) = g.app ⊤ (UnitHomTopSections.unitHomTopSectionsEquiv M f) := rfl

theorem globalSections_injective_of_mono {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) [Mono f] : Function.Injective (f.app ⊤) := by
  intro x y h
  apply (UnitHomTopSections.unitHomTopSectionsEquiv M).symm.injective
  apply (cancel_mono f).mp
  apply (UnitHomTopSections.unitHomTopSectionsEquiv N).injective
  rw [unitHomTopSectionsEquiv_comp, unitHomTopSectionsEquiv_comp,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsMono
