import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.OrdinaryGlobalLineDescent
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelScalarRecovery
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineRecoveryUniqueness

/-! # Effective Kernel Characters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.EffectiveKernelCharacters

noncomputable section

/-!
# CartierDuality: actual kernel characters construct actual global line bundles
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.KernelCharacters
section

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
    (χ : ∀ T : Over S, (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ)
    (hχ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
      Units.map t.left.appTop.hom (χ T x) = χ U (t ≫ x))

/-- Descend the trivial line with the actual character difference cocycle. -/
def characterDescendedLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left :=
  OrdinaryGlobalLineDescent.Construction.LineDescent.nativeDescendedLine f.left (KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f χ hχ) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial A.left).locallyTrivial

/-- The descended character line has its canonical trivialization on the cover. -/
def characterDescendedLineFrame :
    (Scheme.Modules.pullback f.left).obj (characterDescendedLine f χ hχ).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left :=
  OrdinaryGlobalLineDescent.Construction.LineDescent.nativeDescendedLinePullbackIso f.left (KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f χ hχ)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial A.left).locallyTrivial

/-- Its native gluing is exactly the supplied character gluing. -/
theorem characterDescendedLine_compatible {T : Scheme.{u}} (q : T ⟶ B.left) (x y : T ⟶ A.left)
    (hx : x ≫ f.left = q) (hy : y ≫ f.left = q) :
    DescentRelationMorphisms.Construction.LineDescent.CompatibleAt (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f.left (characterDescendedLine f χ hχ).sheaf)
      (KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f χ hχ) (characterDescendedLineFrame f χ hχ).hom q x y hx hy :=
  OrdinaryGlobalLineDescent.Construction.LineDescent.nativeDescendedLinePullbackIso_compatible f.left (KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f χ hχ)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial A.left).locallyTrivial q x y hx hy

/-- The constructed line evaluates to the original character on all test schemes. -/
theorem characterDescendedLine_kernelValue {T : Over S} (x : T ⟶ A) (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    Picard.Homomorphisms.LineKernelCocycle.Construction.framedKernelScalar f (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f.left (characterDescendedLine f χ hχ).sheaf)
      (characterDescendedLineFrame f χ hχ) x z = (χ T z).val :=
  KernelScalarRecovery.Construction.KernelCharacters.recoveredLine_kernelValue f χ hχ (characterDescendedLine f χ hχ) (characterDescendedLineFrame f χ hχ)
    (characterDescendedLine_compatible f χ hχ) x z

/-- The original global regular character is recovered on the universal kernel element. -/
theorem characterDescendedLine_kernelScalar :
    (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f (characterDescendedLine f χ hχ) (characterDescendedLineFrame f χ hχ)).kernelScalar =
      (χ (Picard.Homomorphisms.Kernel.Construction.kernelScheme f) (𝟙 (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).val :=
  KernelScalarRecovery.Construction.KernelCharacters.recoveredLine_kernelScalar f χ hχ (characterDescendedLine f χ hχ) (characterDescendedLineFrame f χ hχ)
    (characterDescendedLine_compatible f χ hχ)

/-- The constructed line lies in the actual pullback kernel of line-bundle classes. -/
def characterPullbackKernelClass :
    {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass B.left // AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left} :=
  ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (characterDescendedLine f χ hχ), Quotient.sound ⟨characterDescendedLineFrame f χ hχ⟩⟩

end

variable {R C : Type u} [CommRing R] [CommRing C] [HopfAlgebra R C]
    {A B : Over (Spec (.of R))} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
    (i : Characters.Construction.affineHopfGroupScheme R C ≅ Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) (z : GroupLike R C)

/-- The actual global line descended from a Hopf character, with no affineness requirement on B. -/
def hopfCharacterDescendedLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left :=
  characterDescendedLine f (KernelCharacterGluing.Construction.KernelCharacters.hopfKernelUnitHom f i z) (KernelCharacterGluing.Construction.KernelCharacters.hopfKernelUnitHom_natural f i z)

/-- Its chosen trivialization is the canonical invariant recovery map. -/
def hopfCharacterDescendedLineFrame :
    (Scheme.Modules.pullback f.left).obj (hopfCharacterDescendedLine f i z).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left :=
  characterDescendedLineFrame f (KernelCharacterGluing.Construction.KernelCharacters.hopfKernelUnitHom f i z) (KernelCharacterGluing.Construction.KernelCharacters.hopfKernelUnitHom_natural f i z)

/-- Actual global line descent recovers exactly the original Hopf coordinate. -/
theorem hopfCharacterDescendedLine_coordinate :
    (Scheme.ΓSpecIso (.of C)).hom (i.hom.hom.hom.left.appTop
      (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f (hopfCharacterDescendedLine f i z)
        (hopfCharacterDescendedLineFrame f i z)).kernelScalar) = z.val :=
  KernelScalarRecovery.Construction.KernelCharacters.recoveredLine_hopfCoordinate f i z (hopfCharacterDescendedLine f i z)
    (hopfCharacterDescendedLineFrame f i z)
    (characterDescendedLine_compatible f (KernelCharacterGluing.Construction.KernelCharacters.hopfKernelUnitHom f i z) (KernelCharacterGluing.Construction.KernelCharacters.hopfKernelUnitHom_natural f i z))

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.EffectiveKernelCharacters
