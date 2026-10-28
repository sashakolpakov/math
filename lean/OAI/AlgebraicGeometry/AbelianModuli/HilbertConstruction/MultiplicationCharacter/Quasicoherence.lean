import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultiplicationCharacter.Sheaves
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdempotentSheafQuasicoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Image
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LevelMultiplication.Finite
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Quasicoherence

/-! # Quasicoherence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual full-level multiplication pushforward and its character sheaves are quasicoherent. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem Abelian.Schemes.AbelianScheme.multiplicationStructurePushforward_quasicoherent {S : Scheme.{u}} {g N : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (level : A.FullLevel N) :
    (A.multiplicationStructurePushforward N).IsQuasicoherent := by
  have := A.fullLevel_multiplication_isFinite level
  have : (Line.Bundles.structureModule A.scheme.left).IsQuasicoherent :=
    (Line.Bundles.LineBundle.trivial A.scheme.left).isQuasicoherent
  exact Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent (A.multiplication N).left
    (Line.Bundles.structureModule A.scheme.left)

theorem Abelian.Schemes.AbelianScheme.multiplicationCharacterSheaf_quasicoherent {K : Type u} [Field K] {g N : ℕ} [NeZero N]
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (level : A.FullLevel N)
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) :
    (A.multiplicationCharacterSheaf level χ).IsQuasicoherent := by
  have := A.multiplicationStructurePushforward_quasicoherent level
  exact IdempotentSheafQuasicoherence.idempotentSheafSummand_quasicoherent _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
