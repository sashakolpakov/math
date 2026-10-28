import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.WeilCharacterDescent
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationKernelSheafComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.RelativePairing

/-! # Weil Character -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.WeilCharacter.Construction

noncomputable section

/-! The actual native CartierDuality Weil pairing evaluates the character whose
descended line represents its second torsion point. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {A : CartierDuality.PolarizedTorsion.AbelianScheme S} (pol : CartierDuality.PolarizedTorsion.Polarization A) (n : ℕ) (hn : 0 < n)

def canonicalCharacterDualPoint (Q : Over S)
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.toOver) ^ n)))).obj.obj (.op Q)) :
    Q ⟶ pol.dual.abelian := by
  have : IsMonHom (show A.toOver ⟶ pol.dual.abelian from pol.map) := pol.preservesGroup
  have : IsFinite (show A.toOver ⟶ pol.dual.abelian from pol.map).left := pol.finite
  have hc := CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A.toOver pol.dual pol.map n hn
  have : IsFinite ((𝟙 A.toOver) ^ n).left := hc.1
  have : Flat ((𝟙 A.toOver) ^ n).left := hc.2.1
  have : Surjective ((𝟙 A.toOver) ^ n).left := hc.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.toOver) ^ n).left := hc.2.2.2
  exact CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint ((𝟙 A.toOver) ^ n) Q χ pol.dual

theorem canonicalNativeWeilPairing_value_of_character (Q : Over S)
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.toOver) ^ n)))).obj.obj (.op Q))
    (x : Q ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.toOver n) (y : Q ⟶ Torsion.Groups.Construction.nativeTorsionScheme pol.dual.abelian n)
    (hy : y ≫ Torsion.Groups.Construction.nativeTorsionInclusion pol.dual.abelian n = canonicalCharacterDualPoint pol n hn Q χ) :
    (RelativePairing.Construction.canonicalNativeWeilPairing pol n hn).pairValue x y =
      CartierDuality.Evaluation.Construction.CharacterEvaluation.value χ (x ≫ (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A.toOver) n).inv.hom.hom) := by
  have : IsMonHom (show A.toOver ⟶ pol.dual.abelian from pol.map) := pol.preservesGroup
  have : IsFinite (show A.toOver ⟶ pol.dual.abelian from pol.map).left := pol.finite
  have : Flat (show A.toOver ⟶ pol.dual.abelian from pol.map).left := pol.flat
  have : Surjective (show A.toOver ⟶ pol.dual.abelian from pol.map).left := pol.surjective
  have hc := CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A.toOver pol.dual pol.map n hn
  have : IsFinite ((𝟙 A.toOver) ^ n).left := hc.1
  have : Flat ((𝟙 A.toOver) ^ n).left := hc.2.1
  have : Surjective ((𝟙 A.toOver) ^ n).left := hc.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.toOver) ^ n).left := hc.2.2.2
  let K := Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.toOver) ^ n))
  have hK := Picard.Homomorphisms.Kernel.Construction.kernelScheme_finiteLocallyFree ((𝟙 A.toOver) ^ n) ⟨hc.1, hc.2.1, hc.2.2.2⟩
  have : IsFinite K.X.hom := hK.1
  have : Flat K.X.hom := hK.2.1
  have : LocallyOfFinitePresentation K.X.hom := hK.2.2
  let C := CartierDuality.PolarizedTorsion.Construction.cartierDualGroupRepresentation S K
  let ys := (Torsion.SheafComparison.Construction.kernelTorsionSheafIso (Grp.mk pol.dual.abelian) n).hom.hom.app (.op Q) (ULift.up y)
  have hys : (kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk pol.dual.abelian)) n)).hom.app (.op Q) ys =
      ULift.up (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint ((𝟙 A.toOver) ^ n) Q χ pol.dual) :=
    (congrArg (fun a => a.hom.app (.op Q) (ULift.up y))
      (Torsion.SheafComparison.Construction.kernelTorsionSheafIso_inclusion (Grp.mk pol.dual.abelian) n)).trans (congrArg ULift.up hy)
  have hv := WeilCharacterDescent.Construction.weilPairing_value_of_character_line A.toOver pol.representation pol.map n hn C Q χ ys hys
    (x ≫ (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A.toOver) n).inv.hom.hom)
  apply ULift.up_injective
  have hx := MultiplicationKernelSheafComparison.Construction.multiplicationKernelSheafIso_native_value (Grp.mk A.toOver) n Q x
  have hr := Torsion.SheafPairing.Construction.torsionSheafPairingToNative_rightValue (Grp.mk A.toOver) (Grp.mk pol.dual.abelian) n
    (pol.weilPairing n hn) Q x y
  exact hr.trans ((congrArg (CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (A.torsionSheaf n) Q
    ((pol.weilPairing n hn).rightAdjoint.hom.app (.op Q) ys)) hx.symm).trans hv)

theorem canonicalNativePolarizationPairing_value_of_character (Q : Over S)
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.toOver) ^ n)))).obj.obj (.op Q))
    (x y : Q ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.toOver n)
    (hy : y ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.toOver n ≫ pol.map = canonicalCharacterDualPoint pol n hn Q χ) :
    (RelativePairing.Construction.canonicalNativePolarizationPairing pol n hn).pairValue x y =
      CartierDuality.Evaluation.Construction.CharacterEvaluation.value χ (x ≫ (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A.toOver) n).inv.hom.hom) := by
  have : IsMonHom (show A.toOver ⟶ pol.dual.abelian from pol.map) := pol.preservesGroup
  have h : (y ≫ Torsion.Groups.Construction.nativeTorsionMap n pol.map) ≫ Torsion.Groups.Construction.nativeTorsionInclusion pol.dual.abelian n =
      canonicalCharacterDualPoint pol n hn Q χ :=
    (Category.assoc _ _ _).trans ((congrArg (fun a => y ≫ a) (Torsion.Groups.Construction.nativeTorsionMap_inclusion n pol.map)).trans hy)
  exact (RelativePairing.Construction.canonicalNativePolarizationPairing_value pol n hn Q x y).trans
    (canonicalNativeWeilPairing_value_of_character pol n hn Q χ x (y ≫ Torsion.Groups.Construction.nativeTorsionMap n pol.map) h)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.WeilCharacter.Construction
