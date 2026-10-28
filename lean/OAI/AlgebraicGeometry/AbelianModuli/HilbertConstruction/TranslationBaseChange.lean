import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Picard
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BaseChange

/-! # Translation Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Translation and its compatibility with the fiber-product comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {g : ℕ} {S S' : Scheme.{u}}

/-- The total-family comparison is an isomorphism over the original base. -/
def TranslationBaseChange.familyBaseChangeOverIso (X : Over S) (f : S' ⟶ S) (T : Over S') :
    (Over.map f).obj (T ⊗ (Over.pullback f).obj X) ≅ (Over.map f).obj T ⊗ X :=
  Over.isoMk (Picard.BaseChange.familyBaseChangeIso X f T) (by
    change (Picard.BaseChange.familyBaseChangeIso X f T).hom ≫
      (pullback.fst (T.hom ≫ f) X.hom ≫ (T.hom ≫ f)) =
        (pullback.fst T.hom (pullback.snd X.hom f) ≫ T.hom) ≫ f
    rw [Picard.BaseChange.familyBaseChangeIso_hom_fst_assoc, Category.assoc])

@[reassoc (attr := simp)]
theorem TranslationBaseChange.familyBaseChangeOverIso_hom_fst (X : Over S) (f : S' ⟶ S) (T : Over S') :
    (TranslationBaseChange.familyBaseChangeOverIso X f T).hom ≫ fst ((Over.map f).obj T) X =
      (Over.map f).map (fst T ((Over.pullback f).obj X)) := by
  apply Over.OverMorphism.ext
  exact Picard.BaseChange.familyBaseChangeIso_hom_fst X f T

/-- The total-family comparison with the bundled abelian pullback as source. -/
def Abelian.Schemes.AbelianScheme.baseChangeFamilyIso (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (T : Over S') :
    (Over.map f).obj (T ⊗ (A.pullback f).scheme) ≅ (Over.map f).obj T ⊗ A.scheme :=
  TranslationBaseChange.familyBaseChangeOverIso A.scheme f T

@[reassoc (attr := simp)]
theorem Abelian.Schemes.AbelianScheme.baseChangeFamilyIso_hom_fst (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (T : Over S') :
    (A.baseChangeFamilyIso f T).hom ≫ fst ((Over.map f).obj T) A.scheme =
      (Over.map f).map (fst T (A.pullback f).scheme) :=
  TranslationBaseChange.familyBaseChangeOverIso_hom_fst A.scheme f T

/-- Translating successively is translation by the product of the two points. -/
theorem Abelian.Schemes.AbelianScheme.translation_comp (A : Abelian.Schemes.AbelianScheme g S) {T : Over S}
    (a b : T ⟶ A.scheme) : A.translation a ≫ A.translation b = A.translation (a * b) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp only [Category.assoc, Abelian.Schemes.AbelianScheme.translation_snd, MonObj.comp_mul]
    rw [← Category.assoc, Abelian.Schemes.AbelianScheme.translation_fst]
    simp only [mul_left_comm, mul_assoc]

/-- Every translation is an isomorphism, with inverse given by the inverse point. -/
def Abelian.Schemes.AbelianScheme.translationIso (A : Abelian.Schemes.AbelianScheme g S) {T : Over S} (a : T ⟶ A.scheme) :
    T ⊗ A.scheme ≅ T ⊗ A.scheme where
  hom := A.translation a
  inv := A.translation a⁻¹
  hom_inv_id := by rw [Abelian.Schemes.AbelianScheme.translation_comp, mul_inv_cancel, Abelian.Schemes.AbelianScheme.translation_one]
  inv_hom_id := by rw [Abelian.Schemes.AbelianScheme.translation_comp, inv_mul_cancel, Abelian.Schemes.AbelianScheme.translation_one]

/-- Naturality of the base-change point equivalence in a test-scheme map. -/
theorem Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_precomp (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S)
    {T U : Over S'} (a : T ⟶ U) (x : (A.pullback f).Points U) :
    A.baseChangePointsEquiv f T (a ≫ x) =
      (Over.map f).map a ≫ A.baseChangePointsEquiv f U x := by
  apply Over.OverMorphism.ext
  exact Category.assoc _ _ _

@[reassoc (attr := simp)]
theorem Abelian.Schemes.AbelianScheme.baseChangeFamilyIso_hom_snd (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S)
    (T : Over S') :
    (A.baseChangeFamilyIso f T).hom ≫ snd ((Over.map f).obj T) A.scheme =
      A.baseChangePointsEquiv f (T ⊗ (A.pullback f).scheme) (snd T (A.pullback f).scheme) := by
  apply Over.OverMorphism.ext
  exact Picard.BaseChange.familyBaseChangeIso_hom_snd A.scheme f T

/-- The fiber-product comparison intertwines translation before and after
changing the base. -/
theorem Abelian.Schemes.AbelianScheme.translation_baseChange (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (T : Over S')
    (a : T ⟶ (A.pullback f).scheme) :
    (Over.map f).map ((A.pullback f).translation a) ≫
        (A.baseChangeFamilyIso f T).hom =
      (A.baseChangeFamilyIso f T).hom ≫
        A.translation (A.baseChangePointsEquiv f T a) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, Abelian.Schemes.AbelianScheme.baseChangeFamilyIso_hom_fst, Abelian.Schemes.AbelianScheme.translation_fst,
      ← Functor.map_comp]
  · calc
      _ = A.baseChangePointsEquiv f (T ⊗ (A.pullback f).scheme)
          ((A.pullback f).translation a ≫ snd T (A.pullback f).scheme) := by
        rw [Category.assoc, Abelian.Schemes.AbelianScheme.baseChangeFamilyIso_hom_snd,
          ← Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_precomp]
      _ = A.baseChangePointsEquiv f (T ⊗ (A.pullback f).scheme)
          ((fst T (A.pullback f).scheme ≫ a) * snd T (A.pullback f).scheme) := by
        rw [Abelian.Schemes.AbelianScheme.translation_snd]
      _ = A.baseChangePointsEquiv f (T ⊗ (A.pullback f).scheme)
            (fst T (A.pullback f).scheme ≫ a) *
          A.baseChangePointsEquiv f (T ⊗ (A.pullback f).scheme)
            (snd T (A.pullback f).scheme) :=
        (A.baseChangePointsMulEquiv f _).map_mul _ _
      _ = _ := by
        rw [Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_precomp]
        simp only [Category.assoc, Abelian.Schemes.AbelianScheme.translation_snd, MonObj.comp_mul,
          Abelian.Schemes.AbelianScheme.baseChangeFamilyIso_hom_fst_assoc, Abelian.Schemes.AbelianScheme.baseChangeFamilyIso_hom_snd]

/-- The same compatibility on underlying total schemes. -/
theorem Abelian.Schemes.AbelianScheme.translation_baseChange_left (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (T : Over S')
    (a : T ⟶ (A.pullback f).scheme) :
    ((A.pullback f).translation a).left ≫ (Picard.BaseChange.familyBaseChangeIso A.scheme f T).hom =
      (Picard.BaseChange.familyBaseChangeIso A.scheme f T).hom ≫
        (A.translation (A.baseChangePointsEquiv f T a)).left :=
  congrArg (fun h => h.left) (A.translation_baseChange f T a)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
