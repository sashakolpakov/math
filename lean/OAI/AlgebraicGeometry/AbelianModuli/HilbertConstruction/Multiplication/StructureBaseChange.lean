import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.BaseChangeEquivariance
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.StructureRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.SelfPullbackTranslations

/-! # Structure Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual self-base-change morphism for multiplication intertwines the full-level translation action with translation in the second factor. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def Abelian.Schemes.AbelianScheme.multiplicationSelfBaseChangeMap (N : ℕ) :
    (Scheme.Modules.pullback (A.multiplication N).left).obj
        (A.multiplicationStructurePushforward N) ⟶
      (Scheme.Modules.pushforward
        (Limits.pullback.fst (A.multiplication N).left (A.multiplication N).left)).obj
          (Line.Bundles.structureModule (Limits.pullback (A.multiplication N).left (A.multiplication N).left)) :=
  Structure.SheafBaseChange.structureBaseChangeMap (IsPullback.of_hasPullback (A.multiplication N).left
    (A.multiplication N).left).flip

theorem Abelian.Schemes.AbelianScheme.multiplicationSelfBaseChangeMap_intertwines (level : A.FullLevel N)
    (a : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    (Scheme.Modules.pullback (A.multiplication N).left).map
        (A.fullLevelStructureRepresentation level a) ≫ A.multiplicationSelfBaseChangeMap N =
      A.multiplicationSelfBaseChangeMap N ≫
        Structure.PushforwardMorphism.structurePushforwardOverMorphism (A.fullLevelSelfPullbackTranslation level a)
          (Limits.pullback.fst (A.multiplication N).left (A.multiplication N).left)
          (Limits.pullback.fst (A.multiplication N).left (A.multiplication N).left)
          (A.fullLevelSelfPullbackTranslation_fst level a) :=
  Structure.BaseChangeEquivariance.structureBaseChangeMap_intertwines
    (IsPullback.of_hasPullback (A.multiplication N).left (A.multiplication N).left).flip
    (A.fullLevelMultiplicationTranslation level a).left
    (A.fullLevelSelfPullbackTranslation level a)
    (A.fullLevelMultiplicationTranslation level a).w
    (A.fullLevelSelfPullbackTranslation_fst level a)
    (A.fullLevelSelfPullbackTranslation_snd level a)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
