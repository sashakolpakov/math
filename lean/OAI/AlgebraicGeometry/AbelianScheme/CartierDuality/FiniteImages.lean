import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Finite Images -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FiniteImages.Construction.Schemes

/-!
# CartierDuality: finiteness of proper images of finite schemes over a base
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- A surjective image of a finite scheme over a base has finite
fibers over that base. -/
theorem finite_fibers_of_surjective_comp {X Q S : Scheme.{u}} (q : X ⟶ Q) (b : Q ⟶ S)
    [Surjective q] [IsFinite (q ≫ b)] (s : S) : (b ⁻¹' {s}).Finite := by
  apply (((q ≫ b).finite_preimage_singleton s).image q).subset
  intro y hy
  obtain ⟨x, rfl⟩ := q.surjective y
  exact ⟨x, hy, rfl⟩

/-- A proper surjective image of a finite scheme over a base is
finite over that base. -/
theorem finite_of_proper_of_surjective_comp {X Q S : Scheme.{u}} (q : X ⟶ Q) (b : Q ⟶ S)
    [Surjective q] [IsProper b] [IsFinite (q ≫ b)] : IsFinite b := by
  let : LocallyQuasiFinite b :=
    LocallyQuasiFinite.of_finite_preimage_singleton b (finite_fibers_of_surjective_comp q b)
  exact IsFinite.of_isProper_of_locallyQuasiFinite b

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FiniteImages.Construction.Schemes
