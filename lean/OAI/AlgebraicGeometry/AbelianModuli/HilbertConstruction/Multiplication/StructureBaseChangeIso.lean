import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.MorphismStructureBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.TorsorStructureComparison

/-! # Structure Base Change Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual full-level multiplication base change is invertible, and its structure-sheaf comparison with the constant torsor is an isomorphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (level : A.FullLevel N)

include level

theorem Abelian.Schemes.AbelianScheme.multiplicationSelfBaseChangeMap_isIso : IsIso (A.multiplicationSelfBaseChangeMap N) := by
  have := A.fullLevel_multiplication_isFinite level
  exact Affine.MorphismStructureBaseChange.affineMorphism_structureBaseChange_isIso
    (IsPullback.of_hasPullback (A.multiplication N).left (A.multiplication N).left).flip

theorem Abelian.Schemes.AbelianScheme.fullLevelStructureComparison_isIso : IsIso (A.fullLevelStructureComparison level) := by
  have : IsIso (A.multiplicationSelfBaseChangeFunctorMap N) :=
    A.multiplicationSelfBaseChangeMap_isIso level
  dsimp only [Abelian.Schemes.AbelianScheme.fullLevelStructureComparison]
  infer_instance

def Abelian.Schemes.AbelianScheme.fullLevelStructureComparisonIso :
    (Scheme.Modules.pullback (A.multiplication N).left).obj
        (A.multiplicationStructurePushforward N) ≅
      Constant.StructureRepresentation.constantStructurePushforward A.scheme.left
        (ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) := by
  have := A.fullLevelStructureComparison_isIso level
  exact asIso (A.fullLevelStructureComparison level)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
