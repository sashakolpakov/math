import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicWeilAdjoints
import OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion

/-! # Cartier Duality Weil Adjoints -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityWeilAdjoints

noncomputable section

/-! Endomorphism adjoints for the canonical Weil pairing in the complete
accepted CartierDuality interface. All finite-cover data come from the polarization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom
attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

namespace Construction

variable {S : Scheme} (A : CartierDuality.PolarizedTorsion.AbelianScheme S) (ell : CartierDuality.PolarizedTorsion.Polarization A)
variable (n : ℕ) (hn : 0 < n) (p : A.toOver ⟶ A.toOver) [IsMonHom p]

theorem e56WeilPairing_endomorphism :
    CartierDuality.PolarizedTorsion.ProjectorsAdjoint (CartierDuality.PolarizedTorsion.Polarization.weilPairing ell n hn)
      (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A.toOver p)) n)
      (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap
        (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicCartierNaturality.Construction.nativePicardEndomorphismGroup A.toOver p ell.dual)) n) := by
  have : IsMonHom (show A.toOver ⟶ ell.dual.abelian from ell.map) := ell.preservesGroup
  have : IsFinite (show A.toOver ⟶ ell.dual.abelian from ell.map).left := ell.finite
  have : Flat (show A.toOver ⟶ ell.dual.abelian from ell.map).left := ell.flat
  have : Surjective (show A.toOver ⟶ ell.dual.abelian from ell.map).left := ell.surjective
  have hc := CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A.toOver ell.dual ell.map n hn
  have : IsFinite ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left := hc.1
  have : Flat ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left := hc.2.1
  have : Surjective ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left := hc.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left := hc.2.2.2
  let K := Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.toOver) ^ n))
  have hK := CartierDuality.TorsionGeometry.Construction.Schemes.nativeTorsion_finiteLocallyFree_of_finite_power (Grp.mk A.toOver) n
  have : IsCommMonObj K.X := Picard.Homomorphisms.KernelGroup.Construction.kernelSchemeGroup_commutative ((𝟙 A.toOver) ^ n)
  have : IsFinite K.X.hom := hK.1
  have : Flat K.X.hom := hK.2.1
  have : LocallyOfFinitePresentation K.X.hom := hK.2.2
  exact IntrinsicWeilAdjoints.Construction.nativeWeilPairing_endomorphism A.toOver ell.representation ell.map n hn
    (CartierDuality.PolarizedTorsion.Construction.cartierDualGroupRepresentation S K) p

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityWeilAdjoints
