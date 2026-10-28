import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.IntrinsicAdjoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourcePolarizationAdjoints

/-! # Pairing Adjoints -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PairingAdjoints.Construction

noncomputable section

/-! The source Rosati equation supplies coefficient adjoints for the
actual canonical pairing over locally Noetherian bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourcePolarizationAdjoints.Construction

set_option backward.isDefEq.respectTransparency false in
theorem noetherianNativePolarizationPairing_coefficient_adjoint
    {S : Scheme.{0}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (n : ℕ) (hn : 0 < n)
    (a : NumberField.RingOfIntegers E) (T : Over S)
    (x y : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.abelian.scheme n) :
    (PolarizationAdapter.Construction.noetherianNativePolarizationPairing A.abelian A.dual A.polarization n hn).pairValue
      (x ≫ Torsion.Groups.Construction.nativeTorsionMap n (ρ.map a)) y =
    (PolarizationAdapter.Construction.noetherianNativePolarizationPairing A.abelian A.dual A.polarization n hn).pairValue
      x (y ≫ Torsion.Groups.Construction.nativeTorsionMap n (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a))) := by
  let pol := PolarizationAdapter.Construction.noetherianPolarizationOfHilbertConstruction A.abelian A.dual A.polarization
  have hd : (FrobeniusKernel.IntrinsicCartierNaturality.Construction.nativePicardEndomorphismGroup A.abelian.scheme (ρ.map a) pol.dual).hom.hom =
      FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (ρ.map a) A.dual A.dual :=
    (FrobeniusKernel.UnbundledPicardComparison.Construction.IntrinsicPicardPullback.dualMap_eq_unbundled (ρ.map a) A.dual A.dual).symm
  have he := FrobeniusKernel.CartierDualityPolarizationAdjoints.Construction.e56PolarizationPairing_adjoint (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A.abelian) pol n hn
    (ρ.map a) (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a))
    ((FrobeniusKernel.PicardAdjoints.Construction.rosati_canonicalDual A ρ hρ a).symm.trans
      (congrArg (fun d => A.polarization.isogeny.hom ≫ d) hd.symm))
  exact Torsion.IntrinsicAdjoints.Construction.torsionSheafPairingToNative_adjoint (Grp.mk A.abelian.scheme) (Grp.mk A.abelian.scheme) n
    (pol.torsionPairing n hn) (FrobeniusKernel.IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A.abelian.scheme (ρ.map a))
    (FrobeniusKernel.IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A.abelian.scheme
      (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a))) he T x y

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PairingAdjoints.Construction
