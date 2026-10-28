import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.ParameterEquivalence

/-! # Empty Projective Families -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Over an empty base there is one actual embedded projective Hilbert family, for every polynomial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem EmptyProjectiveFamilies.idealSheaf_eq_bot_of_isEmpty {X : Scheme.{u}} [IsEmpty X] (I : X.IdealSheafData) : I = ⊥ :=
  I.ker_subschemeι.symm.trans (Scheme.Hom.ker_eq_bot_of_isIso I.subschemeι)

variable {T : Scheme.{u}} [IsEmpty T]

def Closed.Families.FlatClosedFamily.overEmpty (P : Over T) : Closed.Families.FlatClosedFamily P where
  ideal := ⊥
  flat := by
    have : IsIso ((⊥ : P.left.IdealSheafData).subschemeι ≫ P.hom) := inferInstance
    infer_instance
  locallyFinitePresentation := by
    have : IsIso ((⊥ : P.left.IdealSheafData).subschemeι ≫ P.hom) := inferInstance
    infer_instance

instance EmptyProjectiveFamilies.flatClosedFamily_subsingleton_of_isEmpty (P : Over T) : Subsingleton (Closed.Families.FlatClosedFamily P) where
  allEq F G := by
    have : IsEmpty P.left := P.hom.base.hom.1.isEmpty
    exact Closed.Families.FlatClosedFamily.ext ((EmptyProjectiveFamilies.idealSheaf_eq_bot_of_isEmpty F.ideal).trans
      (EmptyProjectiveFamilies.idealSheaf_eq_bot_of_isEmpty G.ideal).symm)

def EmptyProjectiveFamilies.emptyRelativeProjectiveHilbertFamily (n : ℕ) (P : Polynomial ℚ) :
    RelativeProjective.Families.RelativeProjectiveHilbertFamily T n P where
  family := Closed.Families.FlatClosedFamily.overEmpty (Projective.ProjectivePresentations.projectiveSpaceOver T n)
  fieldHilbert K _ x := isEmptyElim (x (⊥ : PrimeSpectrum K))

instance EmptyProjectiveFamilies.relativeProjectiveHilbertFamily_subsingleton_of_isEmpty (n : ℕ) (P : Polynomial ℚ) :
    Subsingleton (RelativeProjective.Families.RelativeProjectiveHilbertFamily T n P) where
  allEq F G := RelativeProjective.Families.RelativeProjectiveHilbertFamily.ext (Subsingleton.elim F.family G.family)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
