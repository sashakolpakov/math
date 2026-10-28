import OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModuleSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Standard Smooth Opens -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.StandardSmoothOpens

noncomputable section

/-! Every point of a smooth complex scheme has an actual standard smooth affine neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom]

theorem exists_standardSmooth_affineOpen (x : X.left) :
    ∃ (U : X.left.Opens), IsAffineOpen U ∧ x ∈ U ∧
      (letI := Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℂ X U
       Algebra.IsStandardSmooth ℂ Γ(X.left, U)) := by
  obtain ⟨W, hW, U, hU, hx, e, hstd⟩ := Smooth.exists_isStandardSmooth X.hom x
  have hWtop : W = ⊤ := by
    have : Subsingleton Foundations.Scheme.ProjectiveSpace.complexBase := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
    apply top_unique
    intro z hz
    have hz' : z = X.hom x := Subsingleton.elim _ _
    rw [hz']
    exact e hx
  subst W
  refine ⟨U, hU, hx, ?_⟩
  change ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ U le_top).hom.IsStandardSmooth
  exact (RingHom.isStandardSmooth_respectsIso.cancel_left_isIso
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv (X.hom.appLE ⊤ U le_top)).mpr hstd

end

end OAI.AlgebraicGeometry.Comparison.Betti.StandardSmoothOpens
