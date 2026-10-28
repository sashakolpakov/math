import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Finite Cover Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.FiniteCoverDescent

noncomputable section

/-! A proper morphism dominated by a finite morphism through a
surjective source cover is finite. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem isFinite_of_proper_surjective_composite {X Y Z : Scheme.{u}}
    (q : X ⟶ Y) (f : Y ⟶ Z) [Surjective q] [IsProper f] [IsFinite (q ≫ f)] :
    IsFinite f := by
  have : LocallyQuasiFinite f := by
    apply LocallyQuasiFinite.of_finite_preimage_singleton
    intro z
    have hfin := ((q ≫ f).finite_preimage_singleton z).image q
    have he : q '' ((q ≫ f) ⁻¹' {z}) = f ⁻¹' {z} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        obtain ⟨x, rfl⟩ := q.surjective y
        exact ⟨x, hy, rfl⟩
    exact he ▸ hfin
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.FiniteCoverDescent
