import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.FamilyMapSquare
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardStructureBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.StructureRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LevelMultiplication.Finite
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.BaseChangeEquivariance

/-! # Multiplication Structure Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual multiplication pushforward and its full-level translations commute with passage to every test-scheme family. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def Abelian.Schemes.AbelianScheme.familyMultiplicationMap (N : ℕ) (T : Over S) : (T ⊗ A.scheme).left ⟶ (T ⊗ A.scheme).left :=
  (T ◁ A.multiplication N).left

def Abelian.Schemes.AbelianScheme.familyStructureComparison (N : ℕ) (T : Over S) :
    (Scheme.Modules.pullback (snd T A.scheme).left).obj (A.multiplicationStructurePushforward N) ⟶
      (Scheme.Modules.pushforward (A.familyMultiplicationMap N T)).obj
        (Line.Bundles.structureModule (T ⊗ A.scheme).left) :=
  Structure.SheafBaseChange.structureBaseChangeMap (Cartesian.FamilyMapSquare.cartesianFamilyMapSquare_left T (A.multiplication N))

def Abelian.Schemes.AbelianScheme.fullLevelFamilyDeckTranslation (level : A.FullLevel N) (T : Over S)
    (i : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    (T ⊗ A.scheme).left ⟶ (T ⊗ A.scheme).left :=
  (T ◁ A.basePointTranslation (A.fullLevelBaseTorsionPoints level i).val).left

theorem Abelian.Schemes.AbelianScheme.fullLevelFamilyDeckTranslation_multiplication (level : A.FullLevel N) (T : Over S)
    (i : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    A.fullLevelFamilyDeckTranslation level T i ≫ A.familyMultiplicationMap N T =
      A.familyMultiplicationMap N T := by
  have h : (T ◁ A.basePointTranslation (A.fullLevelBaseTorsionPoints level i).val) ≫
      (T ◁ A.multiplication N) = T ◁ A.multiplication N := by
    rw [← whiskerLeft_comp, A.basePointTranslation_multiplication N
      (A.fullLevelBaseTorsionPoints level i).val (A.fullLevelBaseTorsionPoints level i).property]
  exact congrArg Over.Hom.left h

theorem Abelian.Schemes.AbelianScheme.fullLevelFamilyDeckTranslation_snd (level : A.FullLevel N) (T : Over S)
    (i : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    A.fullLevelFamilyDeckTranslation level T i ≫ (snd T A.scheme).left =
      (snd T A.scheme).left ≫ (A.fullLevelMultiplicationTranslation level i).left := by
  exact congrArg Over.Hom.left
    (whiskerLeft_snd T (A.basePointTranslation (A.fullLevelBaseTorsionPoints level i).val))

def Abelian.Schemes.AbelianScheme.fullLevelFamilyStructureTranslation (level : A.FullLevel N) (T : Over S)
    (i : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    End ((Scheme.Modules.pushforward (A.familyMultiplicationMap N T)).obj
      (Line.Bundles.structureModule (T ⊗ A.scheme).left)) :=
  Structure.PushforwardMorphism.structurePushforwardOverMorphism (A.fullLevelFamilyDeckTranslation level T i)
    (A.familyMultiplicationMap N T) (A.familyMultiplicationMap N T)
      (A.fullLevelFamilyDeckTranslation_multiplication level T i)

theorem Abelian.Schemes.AbelianScheme.familyStructureComparison_intertwines (level : A.FullLevel N) (T : Over S)
    (i : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    (Scheme.Modules.pullback (snd T A.scheme).left).map (A.fullLevelStructureRepresentation level i) ≫
      A.familyStructureComparison N T =
    A.familyStructureComparison N T ≫ A.fullLevelFamilyStructureTranslation level T i :=
  Structure.BaseChangeEquivariance.structureBaseChangeMap_intertwines (Cartesian.FamilyMapSquare.cartesianFamilyMapSquare_left T (A.multiplication N))
    (A.fullLevelMultiplicationTranslation level i).left (A.fullLevelFamilyDeckTranslation level T i)
    (A.fullLevelMultiplicationTranslation level i).w
    (A.fullLevelFamilyDeckTranslation_multiplication level T i)
    (A.fullLevelFamilyDeckTranslation_snd level T i)

variable (level : A.FullLevel N)
include level

theorem Abelian.Schemes.AbelianScheme.familyMultiplication_isFinite (T : Over S) : IsFinite (A.familyMultiplicationMap N T) := by
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite)
    (Cartesian.FamilyMapSquare.cartesianFamilyMapSquare_left T (A.multiplication N)) (A.fullLevel_multiplication_isFinite level)

theorem Abelian.Schemes.AbelianScheme.familyStructureComparison_isIso (T : Over S) : IsIso (A.familyStructureComparison N T) := by
  have := A.fullLevel_multiplication_isFinite level
  exact Affine.PushforwardStructureBaseChange.affinePushforward_structureBaseChange_isIso (Cartesian.FamilyMapSquare.cartesianFamilyMapSquare_left T (A.multiplication N))

def Abelian.Schemes.AbelianScheme.familyStructureComparisonIso (T : Over S) :
    (Scheme.Modules.pullback (snd T A.scheme).left).obj (A.multiplicationStructurePushforward N) ≅
      (Scheme.Modules.pushforward (A.familyMultiplicationMap N T)).obj
        (Line.Bundles.structureModule (T ⊗ A.scheme).left) := by
  have := A.familyStructureComparison_isIso level T
  exact asIso (A.familyStructureComparison N T)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
