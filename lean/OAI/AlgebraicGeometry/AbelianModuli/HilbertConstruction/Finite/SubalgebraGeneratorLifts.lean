import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! # Subalgebra Generator Lifts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.SubalgebraGeneratorLifts

noncomputable section

/-! A finite family generating an ambient subalgebra also generates
that subalgebra internally after lifting its elements. -/
open scoped Classical
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

def finiteSubalgebraGeneratorLift (S : Subalgebra R A) (F : Finset A)
    (hF : ∀ x ∈ F, x ∈ S) : F → S := fun x => ⟨x.val, hF x.val x.property⟩

theorem finiteSubalgebraGeneratorLift_adjoin (S : Subalgebra R A) (F : Finset A)
    (hF : ∀ x ∈ F, x ∈ S) (hgen : Algebra.adjoin R (F : Set A) = S) :
    Algebra.adjoin R (Set.range (finiteSubalgebraGeneratorLift S F hF)) = ⊤ := by
  apply Subalgebra.map_injective (f := S.val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
  have he : S.val '' Set.range (finiteSubalgebraGeneratorLift S F hF) = (F : Set A) := by
    ext x
    constructor
    · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
      exact j.property
    · intro hx
      exact ⟨finiteSubalgebraGeneratorLift S F hF ⟨x, hx⟩, Set.mem_range_self _, rfl⟩
  rw [he, hgen]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.SubalgebraGeneratorLifts
