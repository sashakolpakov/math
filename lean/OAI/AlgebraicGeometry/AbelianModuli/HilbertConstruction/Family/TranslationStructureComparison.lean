import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.TranslationSquares
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.ComparisonTransport

/-! # Translation Structure Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Canonical family translation comparisons preserve the actual full-level action and transport back to the pullback of the original multiplication pushforward. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def Abelian.Schemes.AbelianScheme.familyTranslationStructureComparison (N : ℕ) {T : Over S} (a : T ⟶ A.scheme) :
    (Scheme.Modules.pullback (A.translation (a ^ N)).left).obj
      ((Scheme.Modules.pushforward (A.familyMultiplicationMap N T)).obj
        (Line.Bundles.structureModule (T ⊗ A.scheme).left)) ⟶
    (Scheme.Modules.pushforward (A.familyMultiplicationMap N T)).obj
      (Line.Bundles.structureModule (T ⊗ A.scheme).left) :=
  Structure.SheafBaseChange.structureBaseChangeMap (A.familyTranslationMultiplicationSquare N a)

theorem Abelian.Schemes.AbelianScheme.familyTranslationStructureComparison_intertwines (level : A.FullLevel N)
    {T : Over S} (a : T ⟶ A.scheme)
    (i : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    (Scheme.Modules.pullback (A.translation (a ^ N)).left).map
      (A.fullLevelFamilyStructureTranslation level T i) ≫ A.familyTranslationStructureComparison N a =
    A.familyTranslationStructureComparison N a ≫ A.fullLevelFamilyStructureTranslation level T i :=
  Structure.BaseChangeEquivariance.structureBaseChangeMap_intertwines (A.familyTranslationMultiplicationSquare N a)
    (A.fullLevelFamilyDeckTranslation level T i) (A.fullLevelFamilyDeckTranslation level T i)
    (A.fullLevelFamilyDeckTranslation_multiplication level T i)
    (A.fullLevelFamilyDeckTranslation_multiplication level T i)
    (A.fullLevelFamilyDeckTranslation_comm level a i)

variable (level : A.FullLevel N)
include level

theorem Abelian.Schemes.AbelianScheme.familyTranslationStructureComparison_isIso {T : Over S} (a : T ⟶ A.scheme) :
    IsIso (A.familyTranslationStructureComparison N a) := by
  have := A.familyMultiplication_isFinite level T
  exact Affine.PushforwardStructureBaseChange.affinePushforward_structureBaseChange_isIso (A.familyTranslationMultiplicationSquare N a)

def Abelian.Schemes.AbelianScheme.familyTranslationStructureComparisonIso {T : Over S} (a : T ⟶ A.scheme) :
    (Scheme.Modules.pullback (A.translation (a ^ N)).left).obj
      ((Scheme.Modules.pushforward (A.familyMultiplicationMap N T)).obj
        (Line.Bundles.structureModule (T ⊗ A.scheme).left)) ≅
    (Scheme.Modules.pushforward (A.familyMultiplicationMap N T)).obj
      (Line.Bundles.structureModule (T ⊗ A.scheme).left) := by
  have := A.familyTranslationStructureComparison_isIso level a
  exact asIso (A.familyTranslationStructureComparison N a)

def Abelian.Schemes.AbelianScheme.familyTranslationComparisonIso {T : Over S} (a : T ⟶ A.scheme) :
    (Scheme.Modules.pullback (A.translation (a ^ N)).left).obj
      ((Scheme.Modules.pullback (snd T A.scheme).left).obj (A.multiplicationStructurePushforward N)) ≅
    (Scheme.Modules.pullback (snd T A.scheme).left).obj (A.multiplicationStructurePushforward N) :=
  Sheaf.ComparisonTransport.sheafComparisonTransport (Scheme.Modules.pullback (A.translation (a ^ N)).left)
    (A.familyStructureComparisonIso level T) (A.familyTranslationStructureComparisonIso level a)

theorem Abelian.Schemes.AbelianScheme.familyTranslationComparisonIso_intertwines {T : Over S} (a : T ⟶ A.scheme)
    (i : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    (Scheme.Modules.pullback (A.translation (a ^ N)).left).map
      ((Scheme.Modules.pullback (snd T A.scheme).left).map (A.fullLevelStructureRepresentation level i)) ≫
      (A.familyTranslationComparisonIso level a).hom =
    (A.familyTranslationComparisonIso level a).hom ≫
      (Scheme.Modules.pullback (snd T A.scheme).left).map (A.fullLevelStructureRepresentation level i) :=
  Sheaf.ComparisonTransport.sheafComparisonTransport_intertwines (Scheme.Modules.pullback (A.translation (a ^ N)).left)
    (A.familyStructureComparisonIso level T) (A.familyTranslationStructureComparisonIso level a)
    ((Scheme.Modules.pullback (snd T A.scheme).left).map (A.fullLevelStructureRepresentation level i))
    (A.fullLevelFamilyStructureTranslation level T i)
    (A.familyStructureComparison_intertwines level T i)
    (A.familyTranslationStructureComparison_intertwines level a i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
