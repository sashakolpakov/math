import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledBaseChangePoints
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneous
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationBaseChange

/-! # Unbundled Translation Base Change -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledTranslationBaseChange.Construction.UnbundledPicard

noncomputable section

/-! Dimension-independent base change of actual group-scheme points,
translations, and homogeneous Picard classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationBaseChange
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S S' : Scheme.{u}}

/-- The total-family comparison with the bundled abelian pullback as source. -/
def baseChangeFamilyIso (A : Over S) [GrpObj A] (f : S' ⟶ S) (T : Over S') :
    (Over.map f).obj (T ⊗ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) ≅ (Over.map f).obj T ⊗ A :=
  AbelianModuli.HilbertConstruction.TranslationBaseChange.familyBaseChangeOverIso A f T

@[reassoc (attr := simp)]
theorem baseChangeFamilyIso_hom_fst (A : Over S) [GrpObj A] (f : S' ⟶ S) (T : Over S') :
    ((baseChangeFamilyIso A) f T).hom ≫ fst ((Over.map f).obj T) A =
      (Over.map f).map (fst T (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) :=
  AbelianModuli.HilbertConstruction.TranslationBaseChange.familyBaseChangeOverIso_hom_fst A f T

/-- Naturality of the base-change point equivalence in a test-scheme map. -/
theorem baseChangePointsEquiv_precomp (A : Over S) [GrpObj A] (f : S' ⟶ S)
    {T U : Over S'} (a : T ⟶ U) (x : (UnbundledBaseChangePoints.Construction.UnbundledPicard.Points (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) U) :
    (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A) f T (a ≫ x) =
      (Over.map f).map a ≫ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A) f U x := by
  apply Over.OverMorphism.ext
  exact Category.assoc _ _ _

@[reassoc (attr := simp)]
theorem baseChangeFamilyIso_hom_snd (A : Over S) [GrpObj A] (f : S' ⟶ S)
    (T : Over S') :
    ((baseChangeFamilyIso A) f T).hom ≫ snd ((Over.map f).obj T) A =
      (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A) f (T ⊗ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) (snd T (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) := by
  apply Over.OverMorphism.ext
  exact AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso_hom_snd A f T

/-- The fiber-product comparison intertwines translation before and after
changing the base. -/
theorem translation_baseChange (A : Over S) [GrpObj A] (f : S' ⟶ S) (T : Over S')
    (a : T ⟶ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) :
    (Over.map f).map ((UnbundledHomogeneous.Construction.UnbundledPicard.translation (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) a) ≫
        ((baseChangeFamilyIso A) f T).hom =
      ((baseChangeFamilyIso A) f T).hom ≫
        (UnbundledHomogeneous.Construction.UnbundledPicard.translation A) ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A) f T a) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, baseChangeFamilyIso_hom_fst, UnbundledHomogeneous.Construction.UnbundledPicard.translation_fst,
      ← Functor.map_comp]
  · calc
      _ = (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A) f (T ⊗ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f))
          ((UnbundledHomogeneous.Construction.UnbundledPicard.translation (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) a ≫ snd T (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) := by
        rw [Category.assoc, baseChangeFamilyIso_hom_snd,
          ← baseChangePointsEquiv_precomp]
      _ = (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A) f (T ⊗ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f))
          ((fst T (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f) ≫ a) * snd T (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) := by
        rw [UnbundledHomogeneous.Construction.UnbundledPicard.translation_snd]
      _ = (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A) f (T ⊗ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f))
            (fst T (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f) ≫ a) *
          (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A) f (T ⊗ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f))
            (snd T (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) :=
        ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsMulEquiv A) f _).map_mul _ _
      _ = _ := by
        rw [baseChangePointsEquiv_precomp]
        simp only [Category.assoc, UnbundledHomogeneous.Construction.UnbundledPicard.translation_snd, MonObj.comp_mul,
          baseChangeFamilyIso_hom_fst_assoc, baseChangeFamilyIso_hom_snd]

/-- The same compatibility on underlying total schemes. -/
theorem translation_baseChange_left (A : Over S) [GrpObj A] (f : S' ⟶ S) (T : Over S')
    (a : T ⟶ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) :
    ((UnbundledHomogeneous.Construction.UnbundledPicard.translation (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) a).left ≫ (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A f T).hom =
      (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A f T).hom ≫
        ((UnbundledHomogeneous.Construction.UnbundledPicard.translation A) ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A) f T a)).left :=
  congrArg (fun h => h.left) ((translation_baseChange A) f T a)

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledTranslationBaseChange.Construction.UnbundledPicard
