import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.MultiplicationStructureComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationBaseChange

/-! # Translation Squares -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Family translations give actual Cartesian multiplication squares and commute with the full-level deck translations. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

theorem Abelian.Schemes.AbelianScheme.familyTranslation_multiplication_square (N : ℕ) {T : Over S} (a : T ⟶ A.scheme) :
    (A.translation a).left ≫ A.familyMultiplicationMap N T =
      A.familyMultiplicationMap N T ≫ (A.translation (a ^ N)).left := by
  have h : A.translation a ≫ (T ◁ A.multiplication N) =
      (T ◁ A.multiplication N) ≫ A.translation (a ^ N) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [Category.assoc]
    · calc
        (A.translation a ≫ (T ◁ A.multiplication N)) ≫ snd T A.scheme =
            ((fst T A.scheme ≫ a) * snd T A.scheme) ≫ A.multiplication N := by
          rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, A.translation_snd]
        _ = (fst T A.scheme ≫ a) ^ N * (snd T A.scheme) ^ N := by
          rw [A.comp_multiplication, mul_pow]
        _ = (fst T A.scheme ≫ a ^ N) * (snd T A.scheme ≫ A.multiplication N) := by
          rw [MonObj.comp_pow, A.comp_multiplication]
        _ = ((T ◁ A.multiplication N) ≫ A.translation (a ^ N)) ≫ snd T A.scheme := by
          simp [Category.assoc, MonObj.comp_mul]
  exact congrArg Over.Hom.left h

theorem Abelian.Schemes.AbelianScheme.familyTranslation_left_isIso {T : Over S} (a : T ⟶ A.scheme) :
    IsIso (A.translation a).left :=
  inferInstanceAs (IsIso (((Over.forget S).mapIso (A.translationIso a)).hom))

theorem Abelian.Schemes.AbelianScheme.familyTranslationMultiplicationSquare (N : ℕ) {T : Over S} (a : T ⟶ A.scheme) :
    IsPullback (A.translation a).left (A.familyMultiplicationMap N T)
      (A.familyMultiplicationMap N T) (A.translation (a ^ N)).left := by
  have := A.familyTranslation_left_isIso a
  have := A.familyTranslation_left_isIso (a ^ N)
  exact IsPullback.of_horiz_isIso ⟨A.familyTranslation_multiplication_square N a⟩

theorem Abelian.Schemes.AbelianScheme.basePointTranslation_family (T : Over S) (t : 𝟙_ (Over S) ⟶ A.scheme) :
    T ◁ A.basePointTranslation t = A.translation (toUnit T ≫ t) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp [Abelian.Schemes.AbelianScheme.basePointTranslation, MonObj.comp_mul]

theorem Abelian.Schemes.AbelianScheme.fullLevelFamilyDeckTranslation_comm (level : A.FullLevel N) {T : Over S}
    (a : T ⟶ A.scheme) (i : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    A.fullLevelFamilyDeckTranslation level T i ≫ (A.translation a).left =
      (A.translation a).left ≫ A.fullLevelFamilyDeckTranslation level T i := by
  let t := (A.fullLevelBaseTorsionPoints level i).val
  have h : (T ◁ A.basePointTranslation t) ≫ A.translation a =
      A.translation a ≫ (T ◁ A.basePointTranslation t) := by
    rw [A.basePointTranslation_family T t, A.translation_comp, A.translation_comp,
      mul_comm (toUnit T ≫ t) a]
  exact congrArg Over.Hom.left h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
