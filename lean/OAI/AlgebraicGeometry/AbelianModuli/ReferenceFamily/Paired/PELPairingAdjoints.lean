import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELQuotients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.PairingCrossAdjoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.UnbundledPicardComparison

/-! # PEL Pairing Adjoints -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELPairingAdjoints

noncomputable section

/-! The two actual maps of a paired PEL quotient are adjoint for
the original source and target canonical polarization pairings, at
every positive torsion level and on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T : Over (Spec (.of K))} [IsLocallyNoetherian T.left]
    {A B : PEL.Objects.PELObject P iota N T}

omit [IsLocallyNoetherian T.left] in
theorem pairedPELQuotient_polarization_adjoint (f : PELQuotients.PairedPELQuotient A B n) :
    f.reverse.isogeny.hom ≫ A.polarized.polarization.isogeny.hom =
      B.polarized.polarization.isogeny.hom ≫
        AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.forward.isogeny.hom A.polarized.dual B.polarized.dual := by
  let : EffectiveEpi f.forward.isogeny.hom :=
    PELModuli.IntegralModel.IsogenyFactorizationIs.IsogenyFactorization.effectiveEpi_over_of_fpqc f.forward.isogeny.hom
  exact (IsogenyPolarizationSymmetry.paired_quotient_polarization_adjoint f.forward.isogeny.hom f.reverse.isogeny.hom
    (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.forward.isogeny.hom A.polarized.dual B.polarized.dual)
    A.polarized.polarization.isogeny.hom B.polarized.polarization.isogeny.hom n
    f.forward_reverse f.forward.polarization).symm

theorem pairedPELQuotient_pairing_adjoint (f : PELQuotients.PairedPELQuotient A B n)
    (m : ℕ) (hm : 0 < m) (X : Over T.left)
    (x : X ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.polarized.abelian.scheme m)
    (y : X ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B.polarized.abelian.scheme m) :
    (AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction.noetherianNativePolarizationPairing B.polarized.abelian B.polarized.dual
      B.polarized.polarization m hm).pairValue
        (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap m f.forward.isogeny.hom) y =
    (AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction.noetherianNativePolarizationPairing A.polarized.abelian A.polarized.dual
      A.polarized.polarization m hm).pairValue
        x (y ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap m f.reverse.isogeny.hom) := by
  let pA := AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction.noetherianPolarizationOfHilbertConstruction A.polarized.abelian A.polarized.dual A.polarized.polarization
  let pB := AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction.noetherianPolarizationOfHilbertConstruction B.polarized.abelian B.polarized.dual B.polarized.polarization
  have : IsMonHom (show (AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A.polarized.abelian).toOver ⟶
      (AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction B.polarized.abelian).toOver from f.forward.isogeny.hom) :=
    f.forward.isogeny.preservesGroup
  have : IsMonHom (show (AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction B.polarized.abelian).toOver ⟶
      (AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A.polarized.abelian).toOver from f.reverse.isogeny.hom) :=
    f.reverse.isogeny.preservesGroup
  have hd : (AbelianScheme.FrobeniusKernel.IntrinsicCartierNaturality.Construction.nativePicardPullbackGroup A.polarized.abelian.scheme B.polarized.abelian.scheme
      f.forward.isogeny.hom pA.dual pB.dual).hom.hom =
        AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.forward.isogeny.hom A.polarized.dual B.polarized.dual :=
    (AbelianScheme.FrobeniusKernel.UnbundledPicardComparison.Construction.IntrinsicPicardPullback.dualMap_eq_unbundled f.forward.isogeny.hom A.polarized.dual B.polarized.dual).symm
  have he := Polarization.PairingCrossAdjoints.e56PolarizationPairing_cross_adjoint
    (AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A.polarized.abelian) (AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction B.polarized.abelian)
    pA pB m hm f.forward.isogeny.hom f.reverse.isogeny.hom
    ((pairedPELQuotient_polarization_adjoint f).trans
      (congrArg (fun d => B.polarized.polarization.isogeny.hom ≫ d) hd.symm))
  exact Polarization.PairingCrossAdjoints.torsionSheafPairingToNative_cross_adjoint
    (Grp.mk A.polarized.abelian.scheme) (Grp.mk B.polarized.abelian.scheme) m
    (pA.torsionPairing m hm) (pB.torsionPairing m hm)
    (AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationNaturality.Construction.nativeAbelianGroupHom A.polarized.abelian.scheme B.polarized.abelian.scheme f.forward.isogeny.hom)
    (AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationNaturality.Construction.nativeAbelianGroupHom B.polarized.abelian.scheme A.polarized.abelian.scheme f.reverse.isogeny.hom)
    he X x y

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELPairingAdjoints
