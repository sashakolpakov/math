import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DiagonalLocalization
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ProductDimension
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-! # External Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ExternalDimension

noncomputable section

section

/-! Dimension bounds on the two original affine supports imply the
strict dimension bound for the localized external tensor product. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensor OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensorNaturality OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTor
open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SpectrumRank

variable (K A R : Type) [Field K] [CommRing A] [CommRing R]
  [Algebra K A] [Algebra K R] [Algebra A R] [IsScalarTower K A R]

attribute [local instance] ExternalTensorFunctor.scalar ExternalTensorFunctor.tower

theorem left_contraction (p : PrimeSpectrum (DiagonalTensor.Ring K R)) :
    PrimeSpectrum.comap (DiagonalTensorNaturality.first K A)
        (PrimeSpectrum.comap (DiagonalLocalization.productMap K A R).toRingHom p) =
      PrimeSpectrum.comap (algebraMap A R) (PrimeSpectrum.comap (DiagonalTensorNaturality.first K R) p) := by
  apply PrimeSpectrum.ext
  ext a
  change DiagonalLocalization.productMap K A R (a ⊗ₜ[K] (1 : A)) ∈ p.asIdeal ↔
    algebraMap A R a ⊗ₜ[K] (1 : R) ∈ p.asIdeal
  simp only [DiagonalLocalization.productMap, Algebra.TensorProduct.map_tmul,
    map_one]
  rfl

theorem right_contraction (p : PrimeSpectrum (DiagonalTensor.Ring K R)) :
    PrimeSpectrum.comap (DiagonalSupport.second K A)
        (PrimeSpectrum.comap (DiagonalLocalization.productMap K A R).toRingHom p) =
      PrimeSpectrum.comap (algebraMap A R) (PrimeSpectrum.comap (DiagonalSupport.second K R) p) := by
  apply PrimeSpectrum.ext
  ext a
  change DiagonalLocalization.productMap K A R ((1 : A) ⊗ₜ[K] a) ∈ p.asIdeal ↔
    (1 : R) ⊗ₜ[K] algebraMap A R a ∈ p.asIdeal
  simp only [DiagonalLocalization.productMap, Algebra.TensorProduct.map_tmul,
    map_one]
  rfl

variable [Algebra.FiniteType K A]

theorem ambient_bound (M N : ModuleCat R) [Module.Finite R M] [Module.Finite R N]
    (m n : ℕ)
    (hM : ∀ p ∈ Module.support R M, SpectrumRank.dimension K A (PrimeSpectrum.comap (algebraMap A R) p) ≤ m)
    (hN : ∀ p ∈ Module.support R N, SpectrumRank.dimension K A (PrimeSpectrum.comap (algebraMap A R) p) ≤ n)
    (p : PrimeSpectrum (DiagonalTensor.Ring K R)) (hp : p ∈ Module.support (DiagonalTensor.Ring K R) (DiagonalTor.external K R M N)) :
    SpectrumRank.dimension K (DiagonalTensor.Ring K A) (PrimeSpectrum.comap (DiagonalLocalization.productMap K A R).toRingHom p) ≤
      m + n := by
  let q := PrimeSpectrum.comap (DiagonalLocalization.productMap K A R).toRingHom p
  have h := Tensor.ProductDimension.Quotient.bound K A A
    (PrimeSpectrum.comap (DiagonalTensorNaturality.first K A) q).asIdeal
    (PrimeSpectrum.comap (DiagonalSupport.second K A) q).asIdeal q.asIdeal le_rfl le_rfl
  change SpectrumRank.dimension K (DiagonalTensor.Ring K A) q ≤ SpectrumRank.dimension K A (PrimeSpectrum.comap (DiagonalTensorNaturality.first K A) q) +
    SpectrumRank.dimension K A (PrimeSpectrum.comap (DiagonalSupport.second K A) q) at h
  have hleft := hM _ (ExternalTensorSupport.left K R R M N p hp)
  have hright := hN _ (ExternalTensorSupport.right K R R M N p hp)
  have hl := left_contraction K A R p
  have hr := right_contraction K A R p
  change PrimeSpectrum.comap (DiagonalTensorNaturality.first K A) q = _ at hl
  change PrimeSpectrum.comap (DiagonalSupport.second K A) q = _ at hr
  rw [hl, hr] at h
  exact h.trans (Nat.add_le_add hleft hright)

theorem noetherian (S : Submonoid A) [IsLocalization S R] : IsNoetherianRing (DiagonalTensor.Ring K R) := by
  let : Algebra.EssFiniteType A R := Algebra.EssFiniteType.of_isLocalization R S
  let : Algebra.EssFiniteType K R := Algebra.EssFiniteType.comp K A R
  let : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing K R
  exact Algebra.EssFiniteType.isNoetherianRing R (DiagonalTensor.Ring K R)

variable [IsLocalRing R] (x : PrimeSpectrum A) [IsLocalization x.asIdeal.primeCompl R]

theorem local_bound (M N : ModuleCat R) [Module.Finite R M] [Module.Finite R N]
    (m n d : ℕ)
    (hM : ∀ p ∈ Module.support R M, SpectrumRank.dimension K A (PrimeSpectrum.comap (algebraMap A R) p) ≤ m)
    (hN : ∀ p ∈ Module.support R N, SpectrumRank.dimension K A (PrimeSpectrum.comap (algebraMap A R) p) ≤ n)
    (hd : m + n < d + SpectrumRank.dimension K A x)
    (p : PrimeSpectrum (Local.DiagonalVanishing.localRing K R))
    (hp : p ∈ Module.support (Local.DiagonalVanishing.localRing K R)
      ((ProjectionFormula.Flat.Extension.baseChange (DiagonalTensor.Ring K R) (Local.DiagonalVanishing.localRing K R)).obj (DiagonalTor.external K R M N))) :
    ringKrullDim (Local.DiagonalVanishing.localRing K R ⧸ p.asIdeal) < d := by
  let : Algebra.FiniteType K (DiagonalTensor.Ring K A) := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  let := DiagonalSupport.finite_external K R M N
  have ht := BaseChangeSupport.mem_image (DiagonalTensor.Ring K R) (Local.DiagonalVanishing.localRing K R)
    (DiagonalTor.external K R M N) p hp
  have hb := ambient_bound K A R M N m n hM hN _ ht
  apply SpectrumRank.local_bound K (DiagonalTensor.Ring K A) (Local.DiagonalVanishing.localRing K R)
    (DiagonalLocalization.map K A R)
    (DiagonalLocalization.strict K A R x.asIdeal.primeCompl) p d
  rw [DiagonalLocalization.closed K A R x, DiagonalLocalization.diagonal_dimension K A x]
  exact hb.trans_lt hd

theorem euler_zero (d : ℕ)
    [Algebra (MvPolynomial (Fin d) K) R] [IsScalarTower K (MvPolynomial (Fin d) K) R]
    [Algebra.FormallyUnramified (MvPolynomial (Fin d) K) R] [Module.Flat (MvPolynomial (Fin d) K) R]
    (M N : ModuleCat R) [Module.Finite R M] [Module.Finite R N]
    (m n : ℕ)
    (hM : ∀ p ∈ Module.support R M, SpectrumRank.dimension K A (PrimeSpectrum.comap (algebraMap A R) p) ≤ m)
    (hN : ∀ p ∈ Module.support R N, SpectrumRank.dimension K A (PrimeSpectrum.comap (algebraMap A R) p) ≤ n)
    (hd : m + n < d + SpectrumRank.dimension K A x)
    (hi : Module.support R M ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R}) :
    Tor.Euler.euler R M N d = 0 := by
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  let : IsNoetherianRing R := IsLocalization.isNoetherianRing x.asIdeal.primeCompl R inferInstance
  let := noetherian K A R x.asIdeal.primeCompl
  exact Local.DiagonalVanishing.euler_zero K R d M N hi
    (local_bound K A R x M N m n d hM hN hd)

end

/-! Native Tor Euler vanishing for the localization of a standard
smooth affine algebra. The etale polynomial presentation and all
diagonal hypotheses are obtained from standard smoothness. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory

namespace StandardSmoothEuler

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SpectrumRank

theorem euler_zero (K A R : Type) [Field K] [CommRing A] [CommRing R]
    [Algebra K A] [Algebra K R] [Algebra A R] [IsScalarTower K A R] [IsLocalRing R]
    (d : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension d K A]
    (x : PrimeSpectrum A) [IsLocalization x.asIdeal.primeCompl R]
    (M N : ModuleCat R) [Module.Finite R M] [Module.Finite R N]
    (m n : ℕ)
    (hM : ∀ p ∈ Module.support R M, SpectrumRank.dimension K A (PrimeSpectrum.comap (algebraMap A R) p) ≤ m)
    (hN : ∀ p ∈ Module.support R N, SpectrumRank.dimension K A (PrimeSpectrum.comap (algebraMap A R) p) ≤ n)
    (hd : m + n < d + SpectrumRank.dimension K A x)
    (hi : Module.support R M ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R}) :
    Tor.Euler.euler R M N d = 0 := by
  let : Algebra.IsStandardSmooth K A := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial d K A
  let P := MvPolynomial (Fin d) K
  let := g.toRingHom.toAlgebra
  let : IsScalarTower K P A := IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  let : Algebra.Etale P A := RingHom.etale_algebraMap.mp hg
  let : Algebra P R := ((algebraMap A R).comp (algebraMap P A)).toAlgebra
  let : IsScalarTower P A R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower K P R := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply K A R, IsScalarTower.algebraMap_apply K P A]
    rfl
  let : Module.Flat A R := IsLocalization.flat R x.asIdeal.primeCompl
  let : Module.Flat P R := Module.Flat.trans P A R
  let : Algebra.FormallyUnramified A R := Algebra.FormallyUnramified.of_isLocalization x.asIdeal.primeCompl
  let : Algebra.FormallyUnramified P R := Algebra.FormallyUnramified.comp P A R
  exact ExternalDimension.euler_zero K A R x d M N m n hM hN hd hi

end StandardSmoothEuler

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ExternalDimension
