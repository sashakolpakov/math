import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.ScalarUnitCharacter
import OAI.AlgebraicGeometry.Picard.Homomorphisms.LineKernelCocycle
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineProducts

/-! # Character Line Recovery -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.CharacterLineRecovery.Construction

noncomputable section

/-! A line with a pullback frame is recovered by descending the actual
kernel character extracted from that frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.LineKernelCocycle.Construction OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineProducts.Construction.KernelCharacters

universe u

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f]
  [IsIso (fst (Picard.Homomorphisms.Kernel.Construction.kernelScheme f) A).left.appTop]
  (D : Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent f.left) (e : D.module ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)

theorem framedDescentScalar_eq_kernelCharacter {T : Scheme.{u}}
    (q : T ⟶ B.left) (x y : T ⟶ A.left) (hx : x ≫ f.left = q) (hy : y ≫ f.left = q) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar D e q x y hx hy =
      CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.differenceScalar f (ScalarUnitCharacter.Construction.kernelScalarUnitCharacter (Picard.Homomorphisms.LineKernelCocycle.Construction.framedKernelScalarCocycle f D e)) q x y hx hy := by
  let px := CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.coverPoint f q x hx
  let py := CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.coverPoint f q y hy
  let h := (CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.coverPoint_comp f q x hx).trans (CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.coverPoint_comp f q y hy).symm
  let z := CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.kernelDifference f px py h
  have hz : px * (z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) = py := by
    rw [CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.kernelDifference_inclusion, mul_inv_cancel_left]
  have hc := ScalarUnitCharacter.Construction.kernelScalarUnitCharacter_recovers (Picard.Homomorphisms.LineKernelCocycle.Construction.framedKernelScalarCocycle f D e) px z
  have he : Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar D e q x y hx hy =
      Picard.Homomorphisms.LineKernelCocycle.Construction.framedKernelScalar f D e px z :=
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar_congr D e _ _ _ _ _ _ _ _ _ _ hx.symm rfl
      (congrArg Over.Hom.left hz).symm
  exact he.trans hc

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]

theorem kernelCharacterLineRecovery (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
    (s : (Scheme.Modules.pullback f.left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left) :
    Nonempty (L.sheaf ≅ (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f
      (ScalarUnitCharacter.Construction.kernelScalarUnitCharacter (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f L s))
      (ScalarUnitCharacter.Construction.kernelScalarUnitCharacter_natural (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f L s))).sheaf) := by
  apply CartierDuality.CharacterLineProducts.Construction.LineDescent.lineIso_of_framedScalars f.left _ _ s
    (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLineFrame f (ScalarUnitCharacter.Construction.kernelScalarUnitCharacter (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f L s))
      (ScalarUnitCharacter.Construction.kernelScalarUnitCharacter_natural (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f L s)))
  intro T q x y hx hy
  exact (framedDescentScalar_eq_kernelCharacter f (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineNativeDatum f L) s q x y hx hy).trans
    (CartierDuality.CharacterLineProducts.Construction.KernelCharacters.characterDescendedLine_scalar f (ScalarUnitCharacter.Construction.kernelScalarUnitCharacter (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f L s))
      (ScalarUnitCharacter.Construction.kernelScalarUnitCharacter_natural (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f L s)) q x y hx hy).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.CharacterLineRecovery.Construction
