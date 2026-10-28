import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ProjectiveFamilyEquations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SingleDegreeProjectiveEquations

/-! # Single Degree Equations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.SingleDegreeEquations.GradedHilbert

noncomputable section

/-! Every native Hilbert family over an arbitrary affine spectrum test is
cut out by a finite list of homogeneous polynomials of one common degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {R : Type u} [CommRing R] {n : ℕ}

theorem native_affine_single_degree_equations (a : Spec (CommRingCat.of R) ⟶ S)
    (F : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)) :
    ∃ (m N : ℕ) (g : Fin m → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (hg : ∀ j, (g j).IsHomogeneous N),
      (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) ≫
        (Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom).ker = F.val := by
  obtain ⟨J, hfg, hF⟩ := Finite.ProjectiveFamilyEquations.GradedHilbert.native_affine_finite_homogeneous_equations a F
  obtain ⟨m, N, g, hg, hs⟩ := SingleDegreeProjectiveEquations.GradedHilbert.finite_single_degree_projective_equations J hfg
  refine ⟨m, N, g, hg, ?_⟩
  rw [Global.PolynomialInclusion.closedImmersion_comp_iso_ker, ← Projective.Saturation.GradedHilbert.projectiveSaturation_idealSheaf (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg),
    hs, Projective.Saturation.GradedHilbert.projectiveSaturation_idealSheaf]
  exact (Global.PolynomialInclusion.closedImmersion_comp_iso_ker (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J)
    (Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a)).symm.trans hF

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.SingleDegreeEquations.GradedHilbert
