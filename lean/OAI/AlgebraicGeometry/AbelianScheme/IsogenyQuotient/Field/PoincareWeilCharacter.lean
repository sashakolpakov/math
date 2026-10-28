import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.WeilCharacter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareCharacter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PolarizationAdapter

/-! # Poincare Weil Character -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PoincareWeilCharacter.Construction

noncomputable section

/-! The original Poincare character is the actual canonical CartierDuality
polarization character on every affine parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (n : ℕ) (hn : 0 < n)
  {Q : Over (Spec (.of k))} [IsAffine Q.left]

theorem originalPoincareCharacter_canonicalDualPoint (t : Q ⟶ D.abelian.scheme) (ht : t ^ n = 1) :
    Canonical.WeilCharacter.Construction.canonicalCharacterDualPoint (PolarizationAdapter.Construction.fieldPolarizationOfHilbertConstruction A D pol) n hn Q
      (Reference.PoincareCharacter.Construction.originalPolarizationPoincareCharacter D pol n hn t ht) = t := by
  have hc := Reference.PositiveMultiplication.Construction.originalPositiveMultiplication_properties D pol n hn
  have : IsFinite ((𝟙 A.scheme) ^ n).left := hc.1
  have : Flat ((𝟙 A.scheme) ^ n).left := hc.2.1
  have : Surjective ((𝟙 A.scheme) ^ n).left := hc.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.scheme) ^ n).left := hc.2.2.2
  change CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint ((𝟙 A.scheme) ^ n) Q (Poincare.ParameterCharacterSection.Construction.poincareParameterCharacterSection D n t ht)
    (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup = t
  exact Poincare.ParameterCharacterSection.Construction.poincareParameterCharacterSection_dualPoint D n t ht

omit [IsAlgClosed k] [IsAffine Q.left] hn in
theorem originalPolarization_torsionPoint_pow (y : Q ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    (y ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n ≫ pol.isogeny.hom) ^ n = 1 := by
  have hy : (y ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n) ^ n = 1 :=
    (MonObj.comp_pow _ n y).symm.trans
      ((congrArg (fun a => y ≫ a) (Torsion.Groups.Construction.nativeTorsionInclusion_killed A.scheme n)).trans (MonObj.comp_one y))
  rw [← Category.assoc, ← MonObj.pow_comp, hy, MonObj.one_comp]

def fieldPolarizationPairingCharacter (y : Q ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf _ (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)))).obj.obj (.op Q) :=
  Reference.PoincareCharacter.Construction.originalPolarizationPoincareCharacter D pol n hn
    (y ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n ≫ pol.isogeny.hom)
    (originalPolarization_torsionPoint_pow D pol n y)

theorem fieldNativePolarizationPairing_poincare_character
    (x y : Q ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    (PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).pairValue x y =
      CartierDuality.Evaluation.Construction.CharacterEvaluation.value (fieldPolarizationPairingCharacter D pol n hn y)
        (x ≫ (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A.scheme) n).inv.hom.hom) := by
  exact Canonical.WeilCharacter.Construction.canonicalNativePolarizationPairing_value_of_character (PolarizationAdapter.Construction.fieldPolarizationOfHilbertConstruction A D pol) n hn Q
    (fieldPolarizationPairingCharacter D pol n hn y) x y
    (originalPoincareCharacter_canonicalDualPoint D pol n hn
      (y ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n ≫ pol.isogeny.hom)
      (originalPolarization_torsionPoint_pow D pol n y)).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PoincareWeilCharacter.Construction
