import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BaseTranslations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.PushforwardFunctor

/-! # Structure Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The ordered full level acts on the actual multiplication pushforward by pullback of functions along torsion translations. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def Abelian.Schemes.AbelianScheme.multiplicationStructurePushforward (N : ℕ) : A.scheme.left.Modules :=
  (Structure.PushforwardFunctor.structurePushforwardFunctor A.scheme.left).obj (.op (Over.mk (A.multiplication N).left))

def Abelian.Schemes.AbelianScheme.fullLevelStructureRepresentation (level : A.FullLevel N) :
    ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →*
      End (A.multiplicationStructurePushforward N) where
  toFun i := (Structure.PushforwardFunctor.structurePushforwardFunctor A.scheme.left).map
    (A.fullLevelMultiplicationTranslation level i).op
  map_one' := by
    change (Structure.PushforwardFunctor.structurePushforwardFunctor A.scheme.left).map
      (A.fullLevelMultiplicationTranslation level 1).op = 𝟙 _
    rw [A.fullLevelMultiplicationTranslation_one level]
    exact (Structure.PushforwardFunctor.structurePushforwardFunctor A.scheme.left).map_id _
  map_mul' i j := by
    change (Structure.PushforwardFunctor.structurePushforwardFunctor A.scheme.left).map
      (A.fullLevelMultiplicationTranslation level (i * j)).op =
        (Structure.PushforwardFunctor.structurePushforwardFunctor A.scheme.left).map
          (A.fullLevelMultiplicationTranslation level j).op ≫
        (Structure.PushforwardFunctor.structurePushforwardFunctor A.scheme.left).map
          (A.fullLevelMultiplicationTranslation level i).op
    rw [← A.fullLevelMultiplicationTranslation_comp level i j]
    exact (Structure.PushforwardFunctor.structurePushforwardFunctor A.scheme.left).map_comp _ _

theorem Abelian.Schemes.AbelianScheme.fullLevelStructureRepresentation_apply (level : A.FullLevel N)
    (i : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    A.fullLevelStructureRepresentation level i =
      Structure.PushforwardMorphism.structurePushforwardOverMorphism
        (A.basePointTranslation (A.fullLevelBaseTorsionPoints level i).val).left
        (A.multiplication N).left (A.multiplication N).left
        (A.fullLevelMultiplicationTranslation level i).w := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
