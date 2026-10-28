import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RepresentedKernelCharacterMap

/-! # Represented Kernel Character Group -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RepresentedKernelCharacterGroup.Construction

noncomputable section

/-! If the recovered native Picard family preserves the group law,
its actual morphism to the Cartier representative preserves it as well. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B K : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f]
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (Y : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
  (j : uliftYoneda.{u + 1}.obj K ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (op K))
  (hχ : CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f K χ = j.app (op K) (ULift.up (𝟙 K)))

variable [GrpObj K]
  (H : ∀ T : Over S, (T ⟶ K) →* (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T))
  (hH : ∀ (T : Over S) (x : T ⟶ K), H T x = j.app (op T) (ULift.up x))
  (hfaithful : ∀ T : Over S, Function.Injective (CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T))

include hχ hH hfaithful in
theorem representedKernelCharacterMap_isMonHom : IsMonHom (RepresentedKernelCharacterMap.Construction.representedKernelCharacterMap f Y χ) := by
  apply GroupMaps.Construction.isMonHom_of_pointwise
  · intro T
    apply (Y.sectionEquiv T).injective
    apply hfaithful T
    rw [RepresentedKernelCharacterMap.Construction.representedKernelCharacterMap_value f Y j χ hχ, ← hH, map_one, map_one, map_one]
  · intro T x y
    apply (Y.sectionEquiv T).injective
    apply hfaithful T
    rw [map_mul, map_mul, RepresentedKernelCharacterMap.Construction.representedKernelCharacterMap_value f Y j χ hχ,
      RepresentedKernelCharacterMap.Construction.representedKernelCharacterMap_value f Y j χ hχ, RepresentedKernelCharacterMap.Construction.representedKernelCharacterMap_value f Y j χ hχ,
      ← hH, ← hH, ← hH, map_mul]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RepresentedKernelCharacterGroup.Construction
