import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.IntrinsicAdjoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourcePolarizationAdjoints

/-! # Reduced Canonical Adjoints -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedCanonicalAdjoints

noncomputable section

/-! The original Rosati equation gives adjoint coefficient actions for
the actual canonical pairing over reduced locally Noetherian bases,
including the integral evaluation DVR. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourcePolarizationAdjoints.Construction

variable {S : Scheme} [IsReduced S] [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

omit [IsReduced S] [IsLocallyNoetherian S] in
theorem reducedSourceNativeDualMap_eq (p : A.abelian.scheme ⟶ A.abelian.scheme) [IsMonHom p] :
    (AbelianScheme.FrobeniusKernel.IntrinsicCartierNaturality.Construction.nativePicardEndomorphismGroup A.abelian.scheme p
      (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).withPicardGroup).hom.hom =
        AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap p A.dual A.dual :=
  (AbelianScheme.FrobeniusKernel.UnbundledPicardComparison.Construction.IntrinsicPicardPullback.dualMap_eq_unbundled p A.dual A.dual).symm

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

theorem reducedCanonicalTorsionPairing_coefficient_adjoint (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)
    (n : ℕ) (hn : 0 < n) (a : NumberField.RingOfIntegers E) :
    CartierDuality.PolarizedTorsion.ProjectorsAdjoint
      ((AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBasePolarizationOfHilbertConstruction A.abelian A.dual A.polarization).torsionPairing n hn)
      (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap
        (AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A.abelian.scheme (ρ.map a))) n)
      (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap
        (AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A.abelian.scheme
          (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a)))) n) := by
  have hros := AbelianScheme.FrobeniusKernel.PicardAdjoints.Construction.rosati_canonicalDual A ρ hρ a
  have hd := reducedSourceNativeDualMap_eq A (ρ.map a)
  have : IsMonHom (show (AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A.abelian).toOver ⟶
      (AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A.abelian).toOver from ρ.map a) := inferInstanceAs (IsMonHom (ρ.map a))
  have : IsMonHom (show (AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A.abelian).toOver ⟶
      (AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A.abelian).toOver from
      ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a)) :=
    inferInstanceAs (IsMonHom (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a)))
  exact AbelianScheme.FrobeniusKernel.CartierDualityPolarizationAdjoints.Construction.e56PolarizationPairing_adjoint (AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A.abelian)
    (AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBasePolarizationOfHilbertConstruction A.abelian A.dual A.polarization) n hn (ρ.map a)
    (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a))
    (hros.symm.trans (congrArg (fun d => A.polarization.isogeny.hom ≫ d) hd.symm))

theorem reducedNativePolarizationPairing_coefficient_adjoint (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)
    (n : ℕ) (hn : 0 < n) (a : NumberField.RingOfIntegers E) (T : Over S)
    (x y : T ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.abelian.scheme n) :
    (AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A.abelian A.dual A.polarization n hn).pairValue
      (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (ρ.map a)) y =
    (AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A.abelian A.dual A.polarization n hn).pairValue
      x (y ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a))) := by
  have he := reducedCanonicalTorsionPairing_coefficient_adjoint A ρ hρ n hn a
  exact AbelianScheme.IsogenyQuotient.Torsion.IntrinsicAdjoints.Construction.torsionSheafPairingToNative_adjoint (Grp.mk A.abelian.scheme) (Grp.mk A.abelian.scheme) n
    ((AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBasePolarizationOfHilbertConstruction A.abelian A.dual A.polarization).torsionPairing n hn)
    (AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A.abelian.scheme (ρ.map a))
    (AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A.abelian.scheme
      (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a))) he T x y

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedCanonicalAdjoints
