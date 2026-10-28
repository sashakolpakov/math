import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityPolarizationAdjoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityCanonical
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.UnbundledPicardComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardAdjoints

/-! # Source Polarization Adjoints -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourcePolarizationAdjoints

noncomputable section

/-! The original PEL Rosati condition gives conjugate coefficient actions
for the actual canonical CartierDuality pairing used in the kernel prescription. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

namespace Construction

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

omit [IsAlgClosed k] in
theorem sourceNativeDualMap_eq (p : A.abelian.scheme ⟶ A.abelian.scheme) [IsMonHom p] :
    (IntrinsicCartierNaturality.Construction.nativePicardEndomorphismGroup A.abelian.scheme p
      (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).withPicardGroup).hom.hom =
        PicardPullback.Construction.IntrinsicPicardPullback.dualMap p A.dual A.dual :=
  (UnbundledPicardComparison.Construction.IntrinsicPicardPullback.dualMap_eq_unbundled p A.dual A.dual).symm

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

theorem sourceCanonicalPairing_coefficient_adjoint (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)
    (n : ℕ) (hn : 0 < n) (a : NumberField.RingOfIntegers E) :
    CartierDuality.PolarizedTorsion.ProjectorsAdjoint (CartierDualityCanonical.Construction.e56SourceTorsionPairing A n hn)
      (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap
        (IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A.abelian.scheme (ρ.map a))) n)
      (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap
        (IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A.abelian.scheme
          (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a)))) n) := by
  have hros := PicardAdjoints.Construction.rosati_canonicalDual A ρ hρ a
  have hd := sourceNativeDualMap_eq A (ρ.map a)
  have : IsMonHom (show (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver ⟶
      (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver from ρ.map a) := inferInstanceAs (IsMonHom (ρ.map a))
  have : IsMonHom (show (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver ⟶
      (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver from
      ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a)) :=
    inferInstanceAs (IsMonHom (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a)))
  exact CartierDualityPolarizationAdjoints.Construction.e56PolarizationPairing_adjoint (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian)
    (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization) n hn (ρ.map a)
    (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a))
    (hros.symm.trans (congrArg (fun d => A.polarization.isogeny.hom ≫ d) hd.symm))

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourcePolarizationAdjoints
