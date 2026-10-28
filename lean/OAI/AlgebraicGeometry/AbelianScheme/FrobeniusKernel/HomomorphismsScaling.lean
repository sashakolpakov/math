import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HomomorphismsIntrinsic
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Polarization

/-! # Homomorphisms Scaling -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HomomorphismsScaling.Construction

noncomputable section

/-! Translate the proved native Homomorphisms scaling conclusion back to the
original FrobeniusKernel polarization map and its canonical Picard adjoint. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k q]
variable {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)

theorem e57NativeSource_pullback_underlying :
    (Picard.Homomorphisms.Polarizations.Construction.pullbackPolarizationHom q Fact.out
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q))
      (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled D pol)).toMul =
    Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q Fact.out
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) A.scheme ≫
      (Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q Fact.out _
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))).map pol.isogeny.hom ≫
      Picard.Homomorphisms.DualFrobenius.Construction.dualRelativeFrobenius D q Fact.out
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) := by
  rfl

omit [Fact q.Prime] [CharP k q] in
theorem e57NativeSource_nsmul_underlying :
    (q • (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled D pol).hom).toMul =
      letI := Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroup D
      pol.isogeny.hom ^ q := by
  rfl

theorem e57NativeSource_polarization_pullback :
    PolarizationComparison.Construction.polarizationPullbackHom
      (Action.Construction.frobeniusIsogeny q Fact.out
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) A).hom
      D (D.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q Fact.out _
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q))))
      (pol.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q Fact.out _
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))) = pol.isogeny.hom ^ q := by
  have hraw := congrArg Additive.toMul (HomomorphismsIntrinsic.Construction.e57NativeSourceConclusions q k D pol).2.2.2.2
  have h : letI := Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroup D
      Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q Fact.out
          (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) A.scheme ≫
        (Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q Fact.out _
          (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))).map pol.isogeny.hom ≫
        Picard.Homomorphisms.DualFrobenius.Construction.dualRelativeFrobenius D q Fact.out
          (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) = pol.isogeny.hom ^ q :=
    (e57NativeSource_pullback_underlying q k D pol).symm.trans
      (hraw.trans (e57NativeSource_nsmul_underlying q k D pol))
  rw [Picard.Homomorphisms.DualGroupComparison.Construction.dualPicardGroup_eq_given D] at h
  unfold PolarizationComparison.Construction.polarizationPullbackHom
  rw [Polarization.Construction.NativePicardPullback.dualMap_eq_e57]
  exact h

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HomomorphismsScaling.Construction
