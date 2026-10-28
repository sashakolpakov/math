import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterSourceMap
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineBaseChange

/-! # Character Line Source Square -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterLineSourceSquare.Construction

noncomputable section

/-! A square of original group homomorphisms pulls back the actual
descended character line to the line of the restricted kernel character.
The full descent datum and its scalar cocycle are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme} {A B A' B' : Over S}
variable [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
variable (f : A ⟶ B) (f' : A' ⟶ B') [IsMonHom f] [IsMonHom f']
variable (a : A' ⟶ A) (b : B' ⟶ B) [IsMonHom a] [IsMonHom b]
variable (h : a ≫ f = f' ≫ b)
variable (χ : ∀ T : Over S, (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ)
variable (hχ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
  Units.map t.left.appTop.hom (χ T x) = χ U (t ≫ x))

def characterLineDatum_sourceSquareIso :
    (Picard.Homomorphisms.ModuleHomBaseChange.Construction.descentSquareFunctor f.left f'.left b.left a.left (congrArg Over.Hom.left h)).obj
      (CartierDuality.AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData (CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f χ hχ)) ≅
    CartierDuality.AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData
      (CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f' (CharacterSourceMap.Construction.kernelCharacterSourceRestriction f f' a b h χ)
        (CharacterSourceMap.Construction.kernelCharacterSourceRestriction_natural f f' a b h χ hχ)) := by
  apply CartierDuality.ScalarDescentSymmetry.Construction.LineDescent.nativeDatumIso_of_framedScalars f'.left _ _
    (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)) a.left) (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A'.left))
  intro T q x y hx hy
  have hs := CartierDuality.FramedBaseChange.Construction.LineDescent.framedDescentScalar_square f.left f'.left b.left a.left
    (congrArg Over.Hom.left h)
    (CartierDuality.AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData (CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f χ hχ))
    (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)) q x y hx hy
  have hold := CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum_scalar f χ hχ (q ≫ b.left) (x ≫ a.left) (y ≫ a.left)
    (by rw [Category.assoc, ← Over.comp_left, h, Over.comp_left, ← Category.assoc, hx])
    (by rw [Category.assoc, ← Over.comp_left, h, Over.comp_left, ← Category.assoc, hy])
  have hnew := CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum_scalar f' (CharacterSourceMap.Construction.kernelCharacterSourceRestriction f f' a b h χ)
    (CharacterSourceMap.Construction.kernelCharacterSourceRestriction_natural f f' a b h χ hχ) q x y hx hy
  exact hs.trans (hold.trans ((CharacterSourceMap.Construction.differenceScalar_sourceSquare f f' a b h χ hχ q x y hx hy).symm.trans hnew.symm))

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
variable [IsAffineHom f'.left] [Flat f'.left] [Surjective f'.left]

theorem characterDescendedLine_sourceSquare :
    Nonempty ((Scheme.Modules.pullback b.left).obj (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ).sheaf ≅
      (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f' (CharacterSourceMap.Construction.kernelCharacterSourceRestriction f f' a b h χ)
        (CharacterSourceMap.Construction.kernelCharacterSourceRestriction_natural f f' a b h χ hχ)).sheaf) :=
  CartierDuality.CharacterLineBaseChange.Construction.LineDescent.recoveredLine_square_iso f.left f'.left b.left a.left
    (congrArg Over.Hom.left h) (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ)
    (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f' (CharacterSourceMap.Construction.kernelCharacterSourceRestriction f f' a b h χ)
      (CharacterSourceMap.Construction.kernelCharacterSourceRestriction_natural f f' a b h χ hχ))
    (CartierDuality.AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData (CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f χ hχ))
    (CartierDuality.AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData
      (CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f' (CharacterSourceMap.Construction.kernelCharacterSourceRestriction f f' a b h χ)
        (CharacterSourceMap.Construction.kernelCharacterSourceRestriction_natural f f' a b h χ hχ)))
    (CartierDuality.OrdinaryGlobalLineDescent.Construction.LineDescent.nativeDescendedLineRecoveryIso f.left (CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f χ hχ)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial A.left).locallyTrivial)
    (CartierDuality.OrdinaryGlobalLineDescent.Construction.LineDescent.nativeDescendedLineRecoveryIso f'.left
      (CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f' (CharacterSourceMap.Construction.kernelCharacterSourceRestriction f f' a b h χ)
        (CharacterSourceMap.Construction.kernelCharacterSourceRestriction_natural f f' a b h χ hχ))
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial A'.left).locallyTrivial)
    (characterLineDatum_sourceSquareIso f f' a b h χ hχ)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterLineSourceSquare.Construction
