import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.CharacterProjectors
import Mathlib.Algebra.Algebra.Basic

/-! # Translation Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.TranslationRepresentation

noncomputable section

/-! Right translation on regular functions is an actual linear representation, and its character projections have the expected character action. -/
universe u v w
section
variable (R : Type w) [CommRing R] (G : Type v) [Group G]

def regularTranslation (a : G) : Module.End R (G → R) where
  toFun v b := v (b * a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def regularTranslationRepresentation : G →* Module.End R (G → R) where
  toFun := regularTranslation R G
  map_one' := by ext v b; exact congrArg v (mul_one b)
  map_mul' a b := by ext v c; exact congrArg v (mul_assoc c a b).symm

@[simp]
theorem regularTranslationRepresentation_apply (a : G) (v : G → R) (b : G) :
    regularTranslationRepresentation R G a v b = v (b * a) := rfl

end
variable (K : Type u) [Field K] (G : Type v) [CommGroup G] [Fintype G]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (R : Type w) [CommRing R] [Algebra K R]

theorem regularTranslation_characterProjector (χ : G →* Kˣ) (a : G) :
    regularTranslationRepresentation R G a * CharacterProjectors.regularCharacterProjector K G R χ =
      (χ a : K) • CharacterProjectors.regularCharacterProjector K G R χ := by
  ext v b
  change CharacterProjectors.regularCharacterProjector K G R χ v (b * a) = (χ a : K) • CharacterProjectors.regularCharacterProjector K G R χ v b
  rw [Algebra.smul_def]
  simp only [CharacterProjectors.regularCharacterProjector_apply, map_mul, Units.val_mul]
  ring

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.TranslationRepresentation
