import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicWeilNaturality
import OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion

/-! # Cartier Duality Weil Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityWeilNaturality

noncomputable section

/-! The accepted CartierDuality Weil pairing respects native source morphisms.
The positive polarizations supply both multiplication covers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom
attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

namespace Construction

variable {S : Scheme} (A B : CartierDuality.PolarizedTorsion.AbelianScheme S)
variable (ellA : CartierDuality.PolarizedTorsion.Polarization A) (ellB : CartierDuality.PolarizedTorsion.Polarization B)
variable (n : ℕ) (hn : 0 < n) (f : A.toOver ⟶ B.toOver) [IsMonHom f]

theorem e56WeilPairing_morphism (T : Over S)
    (x : (A.torsionSheaf n).obj.obj (.op T))
    (y : (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk ellB.dual.abelian)) n).obj.obj (.op T)) :
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (B.torsionSheaf n) T
      ((ellB.weilPairing n hn).rightAdjoint.hom.app (.op T) y)
      ((CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationNaturality.Construction.nativeAbelianGroupHom A.toOver B.toOver f)) n).hom.app (.op T) x) =
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (A.torsionSheaf n) T
      ((ellA.weilPairing n hn).rightAdjoint.hom.app (.op T)
        ((CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap
          (IntrinsicCartierNaturality.Construction.nativePicardPullbackGroup A.toOver B.toOver f ellA.dual ellB.dual)) n).hom.app (.op T) y)) x := by
  have : IsMonHom (show A.toOver ⟶ ellA.dual.abelian from ellA.map) := ellA.preservesGroup
  have : IsFinite (show A.toOver ⟶ ellA.dual.abelian from ellA.map).left := ellA.finite
  have : Flat (show A.toOver ⟶ ellA.dual.abelian from ellA.map).left := ellA.flat
  have : Surjective (show A.toOver ⟶ ellA.dual.abelian from ellA.map).left := ellA.surjective
  have : IsMonHom (show B.toOver ⟶ ellB.dual.abelian from ellB.map) := ellB.preservesGroup
  have : IsFinite (show B.toOver ⟶ ellB.dual.abelian from ellB.map).left := ellB.finite
  have : Flat (show B.toOver ⟶ ellB.dual.abelian from ellB.map).left := ellB.flat
  have : Surjective (show B.toOver ⟶ ellB.dual.abelian from ellB.map).left := ellB.surjective
  have hA := CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A.toOver ellA.dual ellA.map n hn
  have : IsFinite ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left := hA.1
  have : Flat ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left := hA.2.1
  have : Surjective ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left := hA.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left := hA.2.2.2
  have hB := CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover B.toOver ellB.dual ellB.map n hn
  have : IsFinite ((𝟙 B.toOver : B.toOver ⟶ B.toOver) ^ n).left := hB.1
  have : Flat ((𝟙 B.toOver : B.toOver ⟶ B.toOver) ^ n).left := hB.2.1
  have : Surjective ((𝟙 B.toOver : B.toOver ⟶ B.toOver) ^ n).left := hB.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 B.toOver : B.toOver ⟶ B.toOver) ^ n).left := hB.2.2.2
  let KA := Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.toOver) ^ n))
  have hKA := CartierDuality.TorsionGeometry.Construction.Schemes.nativeTorsion_finiteLocallyFree_of_finite_power (Grp.mk A.toOver) n
  have : IsCommMonObj KA.X := Picard.Homomorphisms.KernelGroup.Construction.kernelSchemeGroup_commutative ((𝟙 A.toOver) ^ n)
  have : IsFinite KA.X.hom := hKA.1
  have : Flat KA.X.hom := hKA.2.1
  have : LocallyOfFinitePresentation KA.X.hom := hKA.2.2
  let KB := Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 B.toOver) ^ n))
  have hKB := CartierDuality.TorsionGeometry.Construction.Schemes.nativeTorsion_finiteLocallyFree_of_finite_power (Grp.mk B.toOver) n
  have : IsCommMonObj KB.X := Picard.Homomorphisms.KernelGroup.Construction.kernelSchemeGroup_commutative ((𝟙 B.toOver) ^ n)
  have : IsFinite KB.X.hom := hKB.1
  have : Flat KB.X.hom := hKB.2.1
  have : LocallyOfFinitePresentation KB.X.hom := hKB.2.2
  exact IntrinsicWeilNaturality.Construction.nativeWeilPairing_morphism A.toOver B.toOver ellA.representation ellB.representation
    ellA.map ellB.map n hn (CartierDuality.PolarizedTorsion.Construction.cartierDualGroupRepresentation S KA)
    (CartierDuality.PolarizedTorsion.Construction.cartierDualGroupRepresentation S KB) f T x y

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityWeilNaturality
