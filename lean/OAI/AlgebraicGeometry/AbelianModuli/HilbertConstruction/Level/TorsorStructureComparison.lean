import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Multiplication.StructureBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.StructureRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ContravariantIsoIntertwining

/-! # Torsor Structure Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual split multiplication torsor identifies its structure pushforward with the constant-torsor structure sheaf, compatibly with translations. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def Abelian.Schemes.AbelianScheme.fullLevelSelfPullbackOverTranslation (level : A.FullLevel N)
    (a : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    End (Over.mk (Limits.pullback.fst (A.multiplication N).left (A.multiplication N).left)) :=
  Over.homMk (A.fullLevelSelfPullbackTranslation level a)
    (A.fullLevelSelfPullbackTranslation_fst level a)

def Abelian.Schemes.AbelianScheme.fullLevelSplitSelfPullbackOverIso (level : A.FullLevel N) :
    ConstantScheme.Iff.constantScheme A.scheme.left (ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) ≅
      Over.mk (Limits.pullback.fst (A.multiplication N).left (A.multiplication N).left) :=
  Over.isoMk (A.fullLevelSplitSelfPullbackIso level) (A.fullLevelSplitSelfPullbackIso_fst level)

theorem Abelian.Schemes.AbelianScheme.fullLevelSplitSelfPullbackOverIso_intertwines (level : A.FullLevel N)
    (a : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    ConstantScheme.Translations.constantSchemeRightTranslation A.scheme.left _ a ≫
        (A.fullLevelSplitSelfPullbackOverIso level).hom =
      (A.fullLevelSplitSelfPullbackOverIso level).hom ≫
        A.fullLevelSelfPullbackOverTranslation level a := by
  apply Over.OverMorphism.ext
  exact A.fullLevelSplitSelfPullbackIso_equivariant level a

def Abelian.Schemes.AbelianScheme.selfPullbackStructurePushforward (N : ℕ) : A.scheme.left.Modules :=
  (Structure.PushforwardFunctor.structurePushforwardFunctor A.scheme.left).obj
    (.op (Over.mk (Limits.pullback.fst (A.multiplication N).left (A.multiplication N).left)))

def Abelian.Schemes.AbelianScheme.fullLevelSelfPullbackStructureTranslation (level : A.FullLevel N)
    (a : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    End (A.selfPullbackStructurePushforward N) :=
  (Structure.PushforwardFunctor.structurePushforwardFunctor A.scheme.left).map (A.fullLevelSelfPullbackOverTranslation level a).op

def Abelian.Schemes.AbelianScheme.fullLevelSelfPullbackStructureIso (level : A.FullLevel N) :
    A.selfPullbackStructurePushforward N ≅
      Constant.StructureRepresentation.constantStructurePushforward A.scheme.left
        (ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :=
  (Structure.PushforwardFunctor.structurePushforwardFunctor A.scheme.left).mapIso (A.fullLevelSplitSelfPullbackOverIso level).op

theorem Abelian.Schemes.AbelianScheme.fullLevelSelfPullbackStructureIso_intertwines (level : A.FullLevel N)
    (a : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    A.fullLevelSelfPullbackStructureTranslation level a ≫
        (A.fullLevelSelfPullbackStructureIso level).hom =
      (A.fullLevelSelfPullbackStructureIso level).hom ≫
        Constant.StructureRepresentation.constantStructureRepresentation A.scheme.left _ a :=
  ContravariantIsoIntertwining.contravariantFunctor_iso_intertwines (Structure.PushforwardFunctor.structurePushforwardFunctor A.scheme.left)
    (A.fullLevelSplitSelfPullbackOverIso level) (ConstantScheme.Translations.constantSchemeRightTranslation A.scheme.left _ a)
    (A.fullLevelSelfPullbackOverTranslation level a)
    (A.fullLevelSplitSelfPullbackOverIso_intertwines level a)

def Abelian.Schemes.AbelianScheme.multiplicationSelfBaseChangeFunctorMap (N : ℕ) :
    (Scheme.Modules.pullback (A.multiplication N).left).obj
      (A.multiplicationStructurePushforward N) ⟶ A.selfPullbackStructurePushforward N :=
  A.multiplicationSelfBaseChangeMap N

theorem Abelian.Schemes.AbelianScheme.multiplicationSelfBaseChangeFunctorMap_intertwines (level : A.FullLevel N)
    (a : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    (Scheme.Modules.pullback (A.multiplication N).left).map
        (A.fullLevelStructureRepresentation level a) ≫ A.multiplicationSelfBaseChangeFunctorMap N =
      A.multiplicationSelfBaseChangeFunctorMap N ≫ A.fullLevelSelfPullbackStructureTranslation level a :=
  A.multiplicationSelfBaseChangeMap_intertwines level a

def Abelian.Schemes.AbelianScheme.fullLevelStructureComparison (level : A.FullLevel N) :
    (Scheme.Modules.pullback (A.multiplication N).left).obj
        (A.multiplicationStructurePushforward N) ⟶
      Constant.StructureRepresentation.constantStructurePushforward A.scheme.left
        (ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :=
  A.multiplicationSelfBaseChangeFunctorMap N ≫ (A.fullLevelSelfPullbackStructureIso level).hom

theorem Abelian.Schemes.AbelianScheme.fullLevelStructureComparison_intertwines (level : A.FullLevel N)
    (a : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    (Scheme.Modules.pullback (A.multiplication N).left).map
        (A.fullLevelStructureRepresentation level a) ≫ A.fullLevelStructureComparison level =
      A.fullLevelStructureComparison level ≫ Constant.StructureRepresentation.constantStructureRepresentation A.scheme.left _ a := by
  rw [Abelian.Schemes.AbelianScheme.fullLevelStructureComparison, ← Category.assoc,
    A.multiplicationSelfBaseChangeFunctorMap_intertwines, Category.assoc,
    A.fullLevelSelfPullbackStructureIso_intertwines, ← Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
