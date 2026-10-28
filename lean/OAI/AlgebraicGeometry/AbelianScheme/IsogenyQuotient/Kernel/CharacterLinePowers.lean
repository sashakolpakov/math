import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterProducts

/-! # Character Line Powers -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.CharacterLinePowers.Construction

noncomputable section

/-! Tensor powers of actual character lines are the lines of the powered
characters. A kernel killed by n therefore gives n-torsion line classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f]
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  (χ : ∀ T : Over S, (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ)
  (hχ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
    Units.map t.left.appTop.hom (χ T x) = χ U (t ≫ x))

include hχ in
omit [IsAffineHom f.left] [Flat f.left] [Surjective f.left] in
theorem kernelUnitCharacter_pow_natural (n : ℕ) {T U : Over S}
    (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    Units.map t.left.appTop.hom (((χ T) ^ n) x) = ((χ U) ^ n) (t ≫ x) := by
  change Units.map t.left.appTop.hom ((χ T x) ^ n) = (χ U (t ≫ x)) ^ n
  rw [map_pow, hχ]

theorem kernelCharacterLine_class_pow (n : ℕ) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f (fun T => (χ T) ^ n)
      (kernelUnitCharacter_pow_natural f χ hχ n)) =
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ)) ^ n := by
  induction n with
  | zero =>
      have he := CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.characterDescendedLine_congr f (fun T => (χ T) ^ 0) (fun _ => 1)
        (kernelUnitCharacter_pow_natural f χ hχ 0) (CartierDuality.CharacterLineProducts.Construction.KernelCharacters.kernelCharacter_one_natural f)
        (funext (fun T => pow_zero (χ T)))
      have hz : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f (fun _ => 1)
          (CartierDuality.CharacterLineProducts.Construction.KernelCharacters.kernelCharacter_one_natural f)) = (1 : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass B.left) :=
        Quotient.sound (CartierDuality.CharacterLineProducts.Construction.KernelCharacters.characterDescendedLine_one f)
      exact (congrArg AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf he).trans
        (hz.trans (pow_zero _).symm)
  | succ n ih =>
      have he := CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.characterDescendedLine_congr f (fun T => (χ T) ^ (n + 1))
        (fun T => (χ T) ^ n * χ T)
        (kernelUnitCharacter_pow_natural f χ hχ (n + 1))
        (CartierDuality.CharacterLineProducts.Construction.KernelCharacters.kernelCharacter_mul_natural f _ χ (kernelUnitCharacter_pow_natural f χ hχ n) hχ)
        (funext (fun T => pow_succ (χ T) n))
      exact (congrArg AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf he).trans
        ((CartierDuality.CharacterLineProducts.Construction.KernelCharacters.characterDescendedLine_class_mul f (fun T => (χ T) ^ n)
          (kernelUnitCharacter_pow_natural f χ hχ n) χ hχ).trans
          ((congrArg (fun c => c * AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ)) ih).trans
            (pow_succ _ n).symm))

include hχ in
theorem kernelCharacterLine_class_torsion (n : ℕ)
    (hn : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ)) ^ n = 1 := by
  have hpow : (fun T => (χ T) ^ n) = (fun _ => 1) := by
    funext T
    apply MonoidHom.ext
    intro x
    change (χ T x) ^ n = 1
    rw [← map_pow, hn, map_one]
  have he := CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.characterDescendedLine_congr f (fun T => (χ T) ^ n) (fun _ => 1)
    (kernelUnitCharacter_pow_natural f χ hχ n) (CartierDuality.CharacterLineProducts.Construction.KernelCharacters.kernelCharacter_one_natural f) hpow
  exact (kernelCharacterLine_class_pow f χ hχ n).symm.trans
    ((congrArg AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf he).trans
      (Quotient.sound (CartierDuality.CharacterLineProducts.Construction.KernelCharacters.characterDescendedLine_one f)))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.CharacterLinePowers.Construction
