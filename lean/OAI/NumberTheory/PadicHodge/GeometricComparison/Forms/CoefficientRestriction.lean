import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.CoefficientIdentity
import OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarRestriction

/-! # Coefficient Restriction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.CoefficientRestriction.FormsCoefficientRestriction

noncomputable section

/-! Equal base coefficients and a compatible scalar tower identify forms with their coordinate-scalar restriction. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [β : Algebra R B] [IsScalarTower R A B]

local instance formTower (n : ℕ) : IsScalarTower R A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n) :=
  IsScalarTower.of_algebraMap_smul (fun r ω =>
    (IsScalarTower.algebraMap_smul B (algebraMap R A r) ω).symm.trans
      ((congrArg (fun b : B => b • ω) (IsScalarTower.algebraMap_apply R A B r).symm).trans
        (IsScalarTower.algebraMap_smul B r ω)))

def iso (α : Algebra R B) (h : α = β) (n : ℕ) : CoefficientIdentity.FormsCoefficientIdentity.module R B α n ≅
    (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A (@AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B _ _ β n)) := by
  letI : Algebra R B := β
  exact CoefficientIdentity.FormsCoefficientIdentity.iso R B α β h n ≪≫ ScalarRestriction.ScalarRestrictionIdentity.iso R A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n)

theorem iso_symbol (α : Algebra R B) (h : α = β) (n : ℕ) (b : B) (v : Fin n → B) :
    (iso R A B (β := β) α h n).hom (@AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B _ _ α n b v) = @AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B _ _ β n b v := by
  let : Algebra R B := β
  exact (ScalarRestriction.ScalarRestrictionIdentity.iso_hom_apply R A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n)
    ((CoefficientIdentity.FormsCoefficientIdentity.iso R B α β h n).hom (@AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B _ _ α n b v))).trans
      (CoefficientIdentity.FormsCoefficientIdentity.iso_symbol R B α β h n b v)

theorem exists_iso_symbols (α : Algebra R B) (h : α = β) (n : ℕ) :
    ∃ e : CoefficientIdentity.FormsCoefficientIdentity.module R B α n ≅
      (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A (@AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B _ _ β n)),
      ∀ (b : B) (v : Fin n → B), e.hom (@AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B _ _ α n b v) =
        @AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B _ _ β n b v := by
  let : Algebra R B := β
  exact ⟨iso R A B (β := β) α h n, iso_symbol R A B (β := β) α h n⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.CoefficientRestriction.FormsCoefficientRestriction
