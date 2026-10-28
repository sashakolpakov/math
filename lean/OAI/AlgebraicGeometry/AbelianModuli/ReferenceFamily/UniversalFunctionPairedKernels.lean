import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELKernelAnnihilator
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationAdapter

/-! # Universal Function Paired Kernels -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniversalFunctionPairedKernels

noncomputable section

/-! The actual paired-quotient kernels are self-annihilating over
arbitrary test bases with universal functions. The pairings are the
original canonical HilbertConstruction polarizations, compared on every scheme point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationAdapter.Construction

theorem universalFunctionNativePolarizationPairing_eq_noetherian
    {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ}
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (D : HilbertConstruction.Dual.Data.DualAbelianData A)
    {δ : Fin g → ℕ} (p : HilbertConstruction.PolarizationData.Polarization D δ)
    (hD : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions D.abelian.scheme) (n : ℕ) (hn : 0 < n) :
    AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing A D p hD n hn =
      AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction.noetherianNativePolarizationPairing A D p n hn := rfl

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T : Over (Spec (.of K))} {A B : PEL.Objects.PELObject P iota N T}

theorem universalFunction_pairedPELQuotient_pairing_adjoint
    (f : Paired.PELQuotients.PairedPELQuotient A B n)
    (hDA : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions A.polarized.dual.abelian.scheme)
    (hDB : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions B.polarized.dual.abelian.scheme)
    (m : ℕ) (hm : 0 < m) (X : Over T.left)
    (x : X ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.polarized.abelian.scheme m)
    (y : X ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B.polarized.abelian.scheme m) :
    (AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing B.polarized.abelian B.polarized.dual
      B.polarized.polarization hDB m hm).pairValue
        (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap m f.forward.isogeny.hom) y =
    (AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing A.polarized.abelian A.polarized.dual
      A.polarized.polarization hDA m hm).pairValue
        x (y ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap m f.reverse.isogeny.hom) := by
  let pA := AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationAdapter.Construction.universalFunctionPolarizationOfHilbertConstruction A.polarized.abelian A.polarized.dual
    A.polarized.polarization hDA
  let pB := AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationAdapter.Construction.universalFunctionPolarizationOfHilbertConstruction B.polarized.abelian B.polarized.dual
    B.polarized.polarization hDB
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
    ((Paired.PELPairingAdjoints.pairedPELQuotient_polarization_adjoint f).trans
      (congrArg (fun d => B.polarized.polarization.isogeny.hom ≫ d) hd.symm))
  exact Polarization.PairingCrossAdjoints.torsionSheafPairingToNative_cross_adjoint
    (Grp.mk A.polarized.abelian.scheme) (Grp.mk B.polarized.abelian.scheme) m
    (pA.torsionPairing m hm) (pB.torsionPairing m hm)
    (AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationNaturality.Construction.nativeAbelianGroupHom A.polarized.abelian.scheme B.polarized.abelian.scheme f.forward.isogeny.hom)
    (AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationNaturality.Construction.nativeAbelianGroupHom B.polarized.abelian.scheme A.polarized.abelian.scheme f.reverse.isogeny.hom)
    he X x y

theorem universalFunction_pairedPELQuotient_forward_kernel_self_annihilating
    (f : Paired.PELQuotients.PairedPELQuotient A B n)
    (hA : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions A.polarized.abelian.scheme)
    (hn : 0 < n) (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2)) :
    let hDA := AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA
    let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.polarized.abelian.scheme n)
      (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.forward.isogeny.hom)
    (AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing A.polarized.abelian A.polarized.dual
      A.polarized.polarization hDA n hn).relativeAnnihilator H = H := by
  let hB := AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source f.forward.isogeny.hom hA
  let hDA := AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA
  let hDB := AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source B.polarized.polarization.isogeny.hom hB
  have h := Paired.PELKernelAnnihilator.paired_torsion_kernel_self_annihilating f.reverse.isogeny.hom f.forward.isogeny.hom
    n f.reverse_forward
    (AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing B.polarized.abelian B.polarized.dual
      B.polarized.polarization hDB n hn)
    (AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing A.polarized.abelian A.polarized.dual
      A.polarized.polarization hDA n hn)
    (AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing_isPerfect B.polarized.abelian B.polarized.dual
      B.polarized.polarization hDB n hn hdegree)
    (universalFunction_pairedPELQuotient_pairing_adjoint f.swap hDB hDA n hn)
  rw [Paired.PELKernelAnnihilator.nativeTorsionMap_kernel_eq] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniversalFunctionPairedKernels
