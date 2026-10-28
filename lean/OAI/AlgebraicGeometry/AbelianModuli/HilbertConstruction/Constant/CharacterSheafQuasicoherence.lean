import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.CharacterSheafSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdempotentSheafQuasicoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Image
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantScheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Quasicoherence

/-! # Character Sheaf Quasicoherence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.CharacterSheafQuasicoherence

noncomputable section

/-! The actual constant-torsor pushforward and all its character summands are quasicoherent. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem constantStructurePushforward_quasicoherent (S : Scheme.{u}) (G : Type u) [Finite G] :
    (StructureRepresentation.constantStructurePushforward S G).IsQuasicoherent := by
  have : (Line.Bundles.structureModule (ConstantScheme.Iff.constantScheme S G).left).IsQuasicoherent :=
    (Line.Bundles.LineBundle.trivial (ConstantScheme.Iff.constantScheme S G).left).isQuasicoherent
  exact Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent (ConstantScheme.Iff.constantScheme S G).hom _

theorem constantCharacterSheaf_quasicoherent {K : Type u} [Field K] {S : Scheme.{u}}
    (c : K →+* Γ(S, ⊤)) (G : Type u) [CommGroup G] [Fintype G] (χ : G →* Kˣ) :
    (CharacterSheafSections.constantCharacterSheaf c G χ).IsQuasicoherent := by
  have := constantStructurePushforward_quasicoherent S G
  exact IdempotentSheafQuasicoherence.idempotentSheafSummand_quasicoherent _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.CharacterSheafQuasicoherence
