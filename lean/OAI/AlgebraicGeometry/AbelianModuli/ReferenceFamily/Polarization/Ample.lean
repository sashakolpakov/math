import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.FiniteMorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.BaseChangeCoherence
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Ample -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.Ample

noncomputable section

/-! Extract an actual ample line bundle from polarization positivity
on the complex abelian scheme itself. Its sections produce a finite
morphism to native complex projective space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {g : ℕ} {δ : Fin g → ℕ} {N : ℕ}
  (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)

theorem polarization_has_ample_line_bundle :
    ∃ L : HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left, L.IsAmple := by
  obtain ⟨L, hL, _⟩ := A.polarization.positive ℂ (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
  let f := A.abelian.pullbackIdIso.inv.left
  let : IsIso f := inferInstanceAs
    (IsIso (((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso A.abelian.pullbackIdIso).inv))
  exact ⟨L.pullback f, hL.pullback_of_isIso f⟩

/-- The finite morphism to actual projective space is constructed from
the polarization's ample line bundle and its covering sections. -/
theorem polarization_finite_projective_morphism :
    ∃ (n : ℕ) (f : A.abelian.scheme.left ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n),
      IsFinite f ∧ f ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n = A.abelian.scheme.hom := by
  obtain ⟨L, hL⟩ := polarization_has_ample_line_bundle A
  obtain ⟨n, f, hf⟩ := hL.exists_finite_projective_morphism A.abelian.scheme.hom
  let : IsFinite f.left := hf
  refine ⟨n, f.left ≫ (Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.complexProjectiveIso n).hom, inferInstance, ?_⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => f.left ≫ q) (Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.complexProjectiveIso_base n)).trans f.w)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.Ample
