import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationCartierIso

/-! # Cartier Map -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.CartierMap

noncomputable section

/-!
Construct the Cartier representative and the actual multiplication
character-line map from an abelian scheme and an isogeny to its Picard
dual. All finite-flat multiplication geometry is proved, not supplied.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

namespace Construction
section

universe u

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.abelian) [IsMonHom ell] [IsFinite ell.left]
    (n : ℕ) (hn : 0 < n)

def multiplicationCartierRepresentation :
    CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))) := by
  obtain ⟨hf, hflat, hs, hfp⟩ := CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A D ell n hn
  have hK := Picard.Homomorphisms.Kernel.Construction.kernelScheme_finiteLocallyFree ((𝟙 A) ^ n) ⟨hf, hflat, hfp⟩
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)).hom := hK.1
  have : Flat (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)).hom := hK.2.1
  have : LocallyOfFinitePresentation (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)).hom := hK.2.2
  exact CartierDuality.PolarizedTorsion.Construction.cartierDualGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n)))

def canonicalMultiplicationCartierMap :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    letI : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
    (multiplicationCartierRepresentation A D ell n hn).dual ⟶
      CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk D.abelian) n := by
  have hcover := CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A D ell n hn
  have : IsFinite ((𝟙 A : A ⟶ A) ^ n).left := hcover.1
  have : Flat ((𝟙 A : A ⟶ A) ^ n).left := hcover.2.1
  have : Surjective ((𝟙 A : A ⟶ A) ^ n).left := hcover.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ n).left := hcover.2.2.2
  exact CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup ((𝟙 A) ^ n) D (multiplicationCartierRepresentation A D ell n hn)
    n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n)

end

universe u

theorem canonicalMultiplicationCartierMap_isIso_geometric
    {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.abelian) [IsMonHom ell]
    [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
    (n : ℕ) (hn : 0 < n)
    (hdegree : ∀ s : Spec (.of k), n.Coprime (ell.left.finrank (η[D.abelian].left s))) :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    letI : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
    IsIso (canonicalMultiplicationCartierMap A D ell n hn) := by
  obtain ⟨hf, hflat, hs, hfp⟩ := CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A D ell n hn
  simpa only [canonicalMultiplicationCartierMap] using MultiplicationCartierIso.Construction.multiplicationCartierToPicardTorsionGroup_isIso A D ell n hn
    (multiplicationCartierRepresentation A D ell n hn) hdegree

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.CartierMap
