import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationIso
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationCovers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData

/-! # Canonical Torsion Cartier Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalTorsionCartierIso

noncomputable section

/-! Apply the actual character-line Cartier-to-dual-torsion isomorphism
proved in CartierDuality at 8878042 to the original polarized abelian scheme.
The coordinate representative is arbitrary; the morphism is CartierDuality's
canonical character-line construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

namespace Construction

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (n : ℕ) (hn : 0 < n)
variable (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k))
  (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.abelian.scheme) ^ n))))

include hn in
omit [IsAlgClosed k] in
theorem polarized_positiveMultiplication_cover :
    IsFinite ((𝟙 A.abelian.scheme : A.abelian.scheme ⟶ A.abelian.scheme) ^ n).left ∧
      Flat ((𝟙 A.abelian.scheme : A.abelian.scheme ⟶ A.abelian.scheme) ^ n).left ∧
      Surjective ((𝟙 A.abelian.scheme : A.abelian.scheme ⟶ A.abelian.scheme) ^ n).left ∧
      LocallyOfFinitePresentation ((𝟙 A.abelian.scheme : A.abelian.scheme ⟶ A.abelian.scheme) ^ n).left := by
  let ell : A.abelian.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).abelian := A.polarization.isogeny.hom
  have : IsMonHom ell := A.polarization.isogeny.preservesGroup
  have : IsFinite ell.left := A.polarization.isogeny.finite
  exact CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A.abelian.scheme (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual) ell n hn

def canonicalTorsionCartierMap :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual)
    letI : IsCommMonObj (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).abelian :=
      Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual)
    C.dual ⟶ CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).abelian) n := by
  have hp := polarized_positiveMultiplication_cover A n hn
  let := hp.1
  let := hp.2.1
  let := hp.2.2.1
  let := hp.2.2.2
  exact CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicardTorsionGroup ((𝟙 A.abelian.scheme) ^ n)
    (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual) C n (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A.abelian.scheme n)

theorem canonicalTorsionCartierMap_isIso :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual)
    letI : IsCommMonObj (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).abelian :=
      Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual)
    IsIso (canonicalTorsionCartierMap A n hn C) := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual)
  have : IsCommMonObj (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).abelian :=
    Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual)
  obtain ⟨hf, hflat, hsurj, hfp⟩ := polarized_positiveMultiplication_cover A n hn
  let := hf
  let := hflat
  let := hsurj
  let := hfp
  let ell : A.abelian.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).abelian := A.polarization.isogeny.hom
  unfold canonicalTorsionCartierMap
  exact @CartierDuality.MultiplicationIso.Construction.KernelCharacters.multiplicationCartierToPicardTorsionGroup_isIso
    k inferInstance inferInstance A.abelian.scheme A.abelian.group A.abelian.commutative
    inferInstance A.abelian.proper A.abelian.connected (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual) ell
    A.polarization.isogeny.preservesGroup A.polarization.isogeny.finite
    A.polarization.isogeny.flat A.polarization.isogeny.surjective n hn hf hflat hsurj hfp C

def canonicalTorsionCartierIso :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual)
    letI : IsCommMonObj (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).abelian :=
      Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual)
    C.dual ≅ CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).abelian) n := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual)
  have : IsCommMonObj (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).abelian :=
    Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual)
  exact @asIso _ _ _ _ (canonicalTorsionCartierMap A n hn C) (canonicalTorsionCartierMap_isIso A n hn C)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalTorsionCartierIso
