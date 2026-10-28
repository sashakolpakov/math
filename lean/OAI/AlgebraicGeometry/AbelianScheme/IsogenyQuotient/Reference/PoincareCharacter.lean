import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ParameterCharacterSection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PositiveMultiplication
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardHomomorphism

/-! # Poincare Character -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareCharacter.Construction

noncomputable section

/-! The original polarization supplies the Poincare character and the
actual Cartier-to-Picard map, with all multiplication geometry discharged. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardHomomorphism.Construction.KernelCharacters

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (n : ℕ) (hn : 0 < n)

def originalPositiveCartierToPicard
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation _ (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)))) :
    C.dual.X ⟶ D.abelian.scheme := by
  have hc := PositiveMultiplication.Construction.originalPositiveMultiplication_properties D pol n hn
  have : IsFinite ((𝟙 A.scheme) ^ n).left := hc.1
  have : Flat ((𝟙 A.scheme) ^ n).left := hc.2.1
  have : Surjective ((𝟙 A.scheme) ^ n).left := hc.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.scheme) ^ n).left := hc.2.2.2
  exact CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard ((𝟙 A.scheme) ^ n) (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) C

variable {Q : Over (Spec (.of k))} [IsAffine Q.left]
  (t : Q ⟶ D.abelian.scheme) (ht : t ^ n = 1)

def originalPolarizationPoincareCharacter :
    (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf _ (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)))).obj.obj (.op Q) := by
  have hc := PositiveMultiplication.Construction.originalPositiveMultiplication_properties D pol n hn
  have : IsFinite ((𝟙 A.scheme) ^ n).left := hc.1
  have : Flat ((𝟙 A.scheme) ^ n).left := hc.2.1
  have : Surjective ((𝟙 A.scheme) ^ n).left := hc.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.scheme) ^ n).left := hc.2.2.2
  exact Poincare.ParameterCharacterSection.Construction.poincareParameterCharacterSection D n t ht

theorem originalPolarizationPoincareCharacter_value {U : Over Q.left}
    (x : U ⟶ (Over.pullback Q.hom).obj A.scheme)
    (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n))) :
    (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter ((𝟙 A.scheme) ^ n) Q (originalPolarizationPoincareCharacter D pol n hn t ht) U z :
      Γ(U.left, ⊤)) = (Poincare.ParameterKernelCharacter.Construction.poincareParameterKernelCocycle D n t ht).value x z := by
  have hc := PositiveMultiplication.Construction.originalPositiveMultiplication_properties D pol n hn
  have : IsFinite ((𝟙 A.scheme) ^ n).left := hc.1
  have : Flat ((𝟙 A.scheme) ^ n).left := hc.2.1
  have : Surjective ((𝟙 A.scheme) ^ n).left := hc.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.scheme) ^ n).left := hc.2.2.2
  change (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter ((𝟙 A.scheme) ^ n) Q (Poincare.ParameterCharacterSection.Construction.poincareParameterCharacterSection D n t ht) U z :
    Γ(U.left, ⊤)) = _
  rw [Poincare.ParameterCharacterSection.Construction.poincareParameterCharacterSection_value]
  exact (Poincare.ParameterKernelCharacter.Construction.poincareParameterKernelCharacter_recovers D n t ht x z).symm

theorem originalPolarizationPoincareCharacter_maps
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation _ (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)))) :
    (C.sectionEquiv Q).symm (originalPolarizationPoincareCharacter D pol n hn t ht) ≫
      originalPositiveCartierToPicard D pol n hn C = t := by
  have hc := PositiveMultiplication.Construction.originalPositiveMultiplication_properties D pol n hn
  have : IsFinite ((𝟙 A.scheme) ^ n).left := hc.1
  have : Flat ((𝟙 A.scheme) ^ n).left := hc.2.1
  have : Surjective ((𝟙 A.scheme) ^ n).left := hc.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.scheme) ^ n).left := hc.2.2.2
  change (C.sectionEquiv Q).symm (Poincare.ParameterCharacterSection.Construction.poincareParameterCharacterSection D n t ht) ≫
    CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard ((𝟙 A.scheme) ^ n) (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) C = t
  rw [CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_apply, MulEquiv.apply_symm_apply]
  exact Poincare.ParameterCharacterSection.Construction.poincareParameterCharacterSection_dualPoint D n t ht

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareCharacter.Construction
