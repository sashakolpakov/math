import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.OverlapSectionUnits
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

/-! # Line Transition Powers -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineTransitionPowers

noncomputable section

/-! In the proved standard-chart frames, actual line-bundle transition
functions on projective space are field scalars times coordinate powers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

universe u
variable (K : Type u) [Field K] {n : ℕ}
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Proj (Hilbert.Polynomial.GradedHilbert.grading K n))) (i j : Fin (n + 1))

def projectiveLineOverlapLeftFrame :
    (Scheme.Modules.pullback (OverlapSectionUnits.projectiveDoubleOpen K i j).ι).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (OverlapSectionUnits.projectiveDoubleOpen K i j).toScheme :=
  Picard.PoincareBundle.Affine.Classification.restrictTrivialization L.sheaf
    ((OverlapSectionUnits.projectiveDoubleOpen_eq_inf K i j).le.trans inf_le_left) (ChartLineFrames.projectiveOpenLineFrame K i L)

def projectiveLineOverlapRightFrame :
    (Scheme.Modules.pullback (OverlapSectionUnits.projectiveDoubleOpen K i j).ι).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (OverlapSectionUnits.projectiveDoubleOpen K i j).toScheme :=
  Picard.PoincareBundle.Affine.Classification.restrictTrivialization L.sheaf
    ((OverlapSectionUnits.projectiveDoubleOpen_eq_inf K i j).le.trans inf_le_right) (ChartLineFrames.projectiveOpenLineFrame K j L)

def projectiveLineOverlapAutomorphism :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (OverlapSectionUnits.projectiveDoubleOpen K i j).toScheme ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (OverlapSectionUnits.projectiveDoubleOpen K i j).toScheme :=
  (projectiveLineOverlapLeftFrame K L i j).symm ≪≫ projectiveLineOverlapRightFrame K L i j

def projectiveLineTransitionValue : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j) :=
  (OverlapSectionUnits.projectiveDoubleOpen K i j).topIso.hom
    (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue (OverlapSectionUnits.projectiveDoubleOpen K i j).toScheme
      (projectiveLineOverlapAutomorphism K L i j).hom)

theorem projectiveLineTransitionValue_isUnit : IsUnit (projectiveLineTransitionValue K L i j) := by
  apply IsUnit.map
  exact (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEnd_isIso_iff (projectiveLineOverlapAutomorphism K L i j).hom).mp inferInstance

def projectiveLineTransitionUnit : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j)ˣ :=
  (projectiveLineTransitionValue_isUnit K L i j).unit

theorem projectiveLineTransitionValue_powers (hji : j ≠ i) :
    ∃ (c : Kˣ) (a b : ℕ), projectiveLineTransitionValue K L i j * OverlapSectionUnits.projectiveOverlapRatio K i j ^ b =
      OverlapSectionUnits.projectiveOverlapConstant K i j (c : K) * OverlapSectionUnits.projectiveOverlapRatio K i j ^ a := by
  obtain ⟨c, a, b, h⟩ := OverlapSectionUnits.projectiveOverlap_unit_powers K i j hji (projectiveLineTransitionUnit K L i j)
  exact ⟨c, a, b, (projectiveLineTransitionValue_isUnit K L i j).unit_spec ▸ h⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineTransitionPowers
