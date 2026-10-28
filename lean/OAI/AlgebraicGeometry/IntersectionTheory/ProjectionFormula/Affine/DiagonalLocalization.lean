import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.LocalizationSpectrum
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.DiagonalVanishing
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SpectrumRank

/-! # Diagonal Localization -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DiagonalLocalization

noncomputable section

/-! The local diagonal spectrum embeds into the finite-type affine
product. Its closed point contracts to the original affine diagonal
point, whose quotient has the original residue-support dimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensor OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensorNaturality

variable (K A R : Type u) [Field K] [CommRing A] [CommRing R]
  [Algebra K A] [Algebra K R] [Algebra A R] [IsScalarTower K A R] [IsLocalRing R]

def productMap : DiagonalTensor.Ring K A →ₐ[K] DiagonalTensor.Ring K R :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A R) (IsScalarTower.toAlgHom K A R)

def map : DiagonalTensor.Ring K A →+* Local.DiagonalVanishing.localRing K R :=
  (algebraMap (DiagonalTensor.Ring K R) (Local.DiagonalVanishing.localRing K R)).comp (productMap K A R).toRingHom

omit [IsLocalRing R] in
theorem product_strict (S : Submonoid A) [IsLocalization S R] :
    StrictMono (PrimeSpectrum.comap (productMap K A R).toRingHom) := by
  have h : (productMap K A R).toRingHom =
      (Tensor.LocalizationSpectrum.rightMap K A R R).comp
        (Tensor.LocalizationSpectrum.leftMap K A R A) := by
    ext a <;> simp [productMap, Tensor.LocalizationSpectrum.rightMap,
      Tensor.LocalizationSpectrum.leftMap]
  intro p q hpq
  rw [h]
  exact Tensor.LocalizationSpectrum.left_strict K A R A S
    (Tensor.LocalizationSpectrum.right_strict K A R R S hpq)

theorem strict (S : Submonoid A) [IsLocalization S R] :
    StrictMono (PrimeSpectrum.comap (DiagonalLocalization.map K A R)) := by
  intro p q hpq
  exact product_strict K A R S
    (Tensor.LocalizationSpectrum.strict_comap (DiagonalTensor.Ring K R)
      (Local.DiagonalVanishing.localRing K R) (DiagonalSupport.point K R).asIdeal.primeCompl hpq)

omit [IsLocalRing R] in
theorem multiplication_natural :
    (DiagonalTensor.multiplication K R).comp (productMap K A R).toRingHom =
      (algebraMap A R).comp (DiagonalTensor.multiplication K A) := by
  ext a <;> simp [DiagonalTensor.multiplication, productMap]

theorem closed (x : PrimeSpectrum A) [IsLocalization x.asIdeal.primeCompl R] :
    PrimeSpectrum.comap (DiagonalLocalization.map K A R) (IsLocalRing.closedPoint (Local.DiagonalVanishing.localRing K R)) =
      PrimeSpectrum.comap (DiagonalTensor.multiplication K A) x := by
  apply PrimeSpectrum.ext
  change ((IsLocalRing.maximalIdeal (Local.DiagonalVanishing.localRing K R)).under
    (DiagonalTensor.Ring K R)).comap
      (productMap K A R).toRingHom = _
  rw [Localization.AtPrime.under_maximalIdeal]
  change (IsLocalRing.maximalIdeal R).comap
    ((DiagonalTensor.multiplication K R).comp (productMap K A R).toRingHom) = _
  rw [multiplication_natural]
  change ((IsLocalRing.maximalIdeal R).under A).comap (DiagonalTensor.multiplication K A) = _
  rw [IsLocalization.AtPrime.under_maximalIdeal R x.asIdeal]
  rfl

omit [Algebra K R] [Algebra A R] [IsScalarTower K A R] [IsLocalRing R] in
theorem diagonal_dimension (x : PrimeSpectrum A) :
    SpectrumRank.dimension K (DiagonalTensor.Ring K A) (PrimeSpectrum.comap (DiagonalTensor.multiplication K A) x) =
      SpectrumRank.dimension K A x := by
  let f : DiagonalTensor.Ring K A →ₐ[K] A ⧸ x.asIdeal :=
    (Ideal.Quotient.mkₐ K x.asIdeal).comp (Algebra.TensorProduct.lmul' K)
  have hf : Function.Surjective f :=
    Ideal.Quotient.mk_surjective.comp (DiagonalSupport.multiplication_surjective K A)
  have hk : RingHom.ker f.toRingHom = (PrimeSpectrum.comap (DiagonalTensor.multiplication K A) x).asIdeal := by
    ext t
    change Ideal.Quotient.mk x.asIdeal (DiagonalTensor.multiplication K A t) = 0 ↔ _
    exact Ideal.Quotient.eq_zero_iff_mem
  let e : (DiagonalTensor.Ring K A ⧸ RingHom.ker f.toRingHom) ≃ₐ[K] (A ⧸ x.asIdeal) :=
    Ideal.quotientKerAlgEquivOfSurjective hf
  have he := AlgEquiv.trdeg_eq (R := K) (A := DiagonalTensor.Ring K A ⧸ RingHom.ker f.toRingHom) e
  rw [hk] at he
  exact congrArg Cardinal.toNat he

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DiagonalLocalization
