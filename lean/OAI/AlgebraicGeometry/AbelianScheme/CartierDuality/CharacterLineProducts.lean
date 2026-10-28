import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TensorCanonicalDescent
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterDualPoints

/-! # Character Line Products -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineProducts

noncomputable section

/-!
# CartierDuality: multiplying actual kernel characters tensors their descended lines
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.LineDescent

/-- Equal full framed gluing scalars descend to an isomorphism of the actual lines. -/
theorem lineIso_of_framedScalars {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] [Flat f] [Surjective f] (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (e : (Scheme.Modules.pullback f).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (d : (Scheme.Modules.pullback f).obj M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (hs : ∀ {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q),
      Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f L.sheaf) e q x y hx hy =
        Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f M.sheaf) d q x y hx hy) :
    Nonempty (L.sheaf ≅ M.sheaf) :=
  ScalarDescentSymmetry.Construction.LineDescent.lineIso_of_ordinaryIso f L M (ScalarDescentSymmetry.Construction.LineDescent.nativeDatumIso_of_framedScalars f _ _ e d hs)

end Construction.LineDescent

namespace Construction.KernelCharacters

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

/-- Naturality of the product character is the actual multiplication of regular units. -/
theorem kernelCharacter_mul_natural
    (χ ψ : ∀ T : Over S, (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ)
    (hχ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
      Units.map t.left.appTop.hom (χ T x) = χ U (t ≫ x))
    (hψ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
      Units.map t.left.appTop.hom (ψ T x) = ψ U (t ≫ x))
    {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    Units.map t.left.appTop.hom ((χ T * ψ T) x) = (χ U * ψ U) (t ≫ x) := by
  rw [MonoidHom.mul_apply, map_mul, hχ, hψ, MonoidHom.mul_apply]

/-- The trivial character is natural on all test schemes. -/
theorem kernelCharacter_one_natural {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    Units.map t.left.appTop.hom ((1 : (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ) x) =
      (1 : (U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(U.left, ⊤)ˣ) (t ≫ x) := by
  apply Units.ext
  change t.left.appTop 1 = 1
  exact t.left.appTop.hom.map_one

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
    (χ : ∀ T : Over S, (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ)
    (hχ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
      Units.map t.left.appTop.hom (χ T x) = χ U (t ≫ x))

/-- The full canonical line datum has the prescribed character difference scalar. -/
theorem characterDescendedLine_scalar {T : Scheme.{u}} (q : T ⟶ B.left) (x y : T ⟶ A.left)
    (hx : x ≫ f.left = q) (hy : y ≫ f.left = q) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f.left (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ).sheaf)
      (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLineFrame f χ hχ) q x y hx hy = KernelCharacterGluing.Construction.KernelCharacters.differenceScalar f χ q x y hx hy :=
  FramedRecovery.Construction.LineDescent.scalarCocycle_recovery (KernelCharacterGluing.Construction.KernelCharacters.characterScalarCocycle f χ hχ) (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ)
    (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLineFrame f χ hχ) q x y hx hy (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine_compatible f χ hχ q x y hx hy)

variable (ψ : ∀ T : Over S, (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ)
    (hψ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
      Units.map t.left.appTop.hom (ψ T x) = ψ U (t ≫ x))

/-- Multiplication of kernel characters is tensor product of the actual descended line bundles. -/
theorem characterDescendedLine_mul :
    Nonempty (((EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ).tensor (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f ψ hψ)).sheaf ≅
      (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f (fun T => χ T * ψ T) (kernelCharacter_mul_natural f χ ψ hχ hψ)).sheaf) := by
  apply LineDescent.lineIso_of_framedScalars f.left _ _
    (TensorCanonicalDescent.Construction.LineDescent.tensorCoverFrame f.left (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ) (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f ψ hψ)
      (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLineFrame f χ hχ) (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLineFrame f ψ hψ))
    (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLineFrame f (fun T => χ T * ψ T) (kernelCharacter_mul_natural f χ ψ hχ hψ))
  intro T q x y hx hy
  have ht := TensorCanonicalDescent.Construction.LineDescent.tensorCanonicalDescent_scalar f.left (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ)
    (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f ψ hψ) (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLineFrame f χ hχ) (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLineFrame f ψ hψ)
    q x y hx hy
  have hχ' := characterDescendedLine_scalar f χ hχ q x y hx hy
  have hψ' := characterDescendedLine_scalar f ψ hψ q x y hx hy
  have hχψ := characterDescendedLine_scalar f (fun T => χ T * ψ T)
    (kernelCharacter_mul_natural f χ ψ hχ hψ) q x y hx hy
  exact ht.trans ((congrArg₂ (· * ·) hχ' hψ').trans hχψ.symm)

/-- Tensor compatibility passes to the intrinsic Picard group of line classes. -/
theorem characterDescendedLine_class_mul :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f (fun T => χ T * ψ T) (kernelCharacter_mul_natural f χ ψ hχ hψ)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ) * AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f ψ hψ) :=
  (Quotient.sound (characterDescendedLine_mul f χ hχ ψ hψ)).symm

/-- The actual line descended from the trivial character is trivial. -/
theorem characterDescendedLine_one :
    Nonempty ((EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f (fun _ => 1) (kernelCharacter_one_natural f)).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left) := by
  apply LineDescent.lineIso_of_framedScalars f.left _ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial B.left)
    (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLineFrame f (fun _ => 1) (kernelCharacter_one_natural f))
    (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left)) f.left)
  intro T q x y hx hy
  have hc := characterDescendedLine_scalar f (fun _ => 1) (kernelCharacter_one_natural f) q x y hx hy
  have hu := congrArg (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T)
    (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent_framedEnd f.left (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left)
      (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left)) q x y hx hy)
  exact hc.trans (hu.trans (map_one (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T))).symm

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineProducts
