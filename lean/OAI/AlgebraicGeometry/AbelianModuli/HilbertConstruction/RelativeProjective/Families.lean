import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.Pullbacks
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.ClosedFamilies

/-! # Families -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.Families

noncomputable section

/-! A relative projective Hilbert family is specified by its actual flat closed family and its field fibers. Every affine pullback has the corresponding Hilbert ideal condition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

structure RelativeProjectiveHilbertFamily (T : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) where
  family : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver T n)
  fieldHilbert : ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ T),
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (family.affineProjectivePullback x).homogeneousIdeal.toIdeal P

variable {T : Scheme.{u}} {n : ℕ} {P : Polynomial ℚ}

def RelativeProjectiveHilbertFamily.affineFamily (F : RelativeProjectiveHilbertFamily T n P)
    {R : CommRingCat.{u}} (x : Spec R ⟶ T) : Flat.ClosedFamilies.FlatClosedHilbertFamily R n P :=
  ⟨F.family.affineProjectivePullback x, by
    intro p
    let A := CommRingCat.of p.asIdeal.ResidueField
    let φ : R ⟶ A := CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField)
    have he := (F.family.affineProjectivePullback x).homogeneousIdeal_coefficientBaseChange φ
    change ((F.family.affineProjectivePullback x).pullbackAlong (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n)
      (Spec.map φ) (Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback φ n)).homogeneousIdeal =
        HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
          (F.family.affineProjectivePullback x).homogeneousIdeal) at he
    rw [← he, ← F.family.affineProjectivePullback_coefficient x φ]
    exact F.fieldHilbert p.asIdeal.ResidueField (Spec.map φ ≫ x)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.Families
