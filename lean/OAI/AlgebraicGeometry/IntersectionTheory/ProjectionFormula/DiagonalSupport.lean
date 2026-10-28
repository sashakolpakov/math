import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExternalTensorFinite
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExternalTensorSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SplitSurjectiveSpectrum

/-! # Diagonal Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalSupport

noncomputable section

/-! Finite inputs with isolated intersection give an isolated pairing
of their external product with the native diagonal, at the corresponding
maximal prime of the product ring. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory
open scoped TensorProduct

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensor OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensorNaturality OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTor

variable (K R : Type u) [Field K] [CommRing R] [Algebra K R]

attribute [local instance] DiagonalTensor.diagonalAlgebra ExternalTensorFunctor.scalar ExternalTensorFunctor.tower

abbrev second : R →+* DiagonalTensor.Ring K R := (Algebra.TensorProduct.includeRight : R →ₐ[K] R ⊗[K] R).toRingHom

theorem multiplication_surjective : Function.Surjective (DiagonalTensor.multiplication K R) :=
  fun r => ⟨DiagonalTensorNaturality.first K R r, mul_one r⟩

theorem first_section : (DiagonalTensor.multiplication K R).comp (DiagonalTensorNaturality.first K R) = RingHom.id R := by
  ext r
  exact mul_one r

theorem finite_external (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N] :
    Module.Finite (DiagonalTensor.Ring K R) (DiagonalTor.external K R M N) := ExternalTensorFinite.finite K R R M N

theorem finite_diagonal : Module.Finite (DiagonalTensor.Ring K R) (DiagonalTensorNaturality.diagonal K R) :=
  Module.Finite.of_surjective (Algebra.linearMap (DiagonalTensor.Ring K R) R) (multiplication_surjective K R)

theorem kernel_le (p : PrimeSpectrum (DiagonalTensor.Ring K R)) (hp : p ∈ Module.support (DiagonalTensor.Ring K R) (DiagonalTensorNaturality.diagonal K R)) :
    RingHom.ker (DiagonalTensor.multiplication K R) ≤ p.asIdeal := by
  change p ∈ Module.support (DiagonalTensor.Ring K R) R at hp
  rw [Module.support_of_algebra] at hp
  exact hp

theorem comaps_eq (p : PrimeSpectrum (DiagonalTensor.Ring K R)) (hp : p ∈ Module.support (DiagonalTensor.Ring K R) (DiagonalTensorNaturality.diagonal K R)) :
    PrimeSpectrum.comap (DiagonalTensorNaturality.first K R) p = PrimeSpectrum.comap (second K R) p := by
  apply PrimeSpectrum.ext
  ext r
  change DiagonalTensorNaturality.first K R r ∈ p.asIdeal ↔ second K R r ∈ p.asIdeal
  have hd : DiagonalTensorNaturality.first K R r - second K R r ∈ p.asIdeal := kernel_le K R p hp (by
    change DiagonalTensor.multiplication K R (DiagonalTensorNaturality.first K R r - second K R r) = 0
    rw [map_sub]
    change r * 1 - 1 * r = 0
    rw [mul_one, one_mul, sub_self])
  constructor
  · intro hr
    simpa only [sub_sub_cancel] using p.asIdeal.sub_mem hr hd
  · intro hr
    simpa only [sub_add_cancel] using p.asIdeal.add_mem hd hr

variable [IsLocalRing R]

def point : PrimeSpectrum (DiagonalTensor.Ring K R) := PrimeSpectrum.comap (DiagonalTensor.multiplication K R) (IsLocalRing.closedPoint R)

theorem maximal : (point K R).asIdeal.IsMaximal := by
  let : (IsLocalRing.closedPoint R).asIdeal.IsMaximal := inferInstanceAs (IsLocalRing.maximalIdeal R).IsMaximal
  exact Ideal.comap_isMaximal_of_surjective (DiagonalTensor.multiplication K R) (multiplication_surjective K R)

theorem isolated (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
    (hp : Module.support R M ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R}) :
    Module.support (DiagonalTensor.Ring K R) (DiagonalTor.external K R M N) ∩ Module.support (DiagonalTensor.Ring K R) (DiagonalTensorNaturality.diagonal K R) ⊆ {point K R} := by
  intro p h
  have hm := ExternalTensorSupport.left K R R M N p h.1
  have hn := ExternalTensorSupport.right K R R M N p h.1
  change PrimeSpectrum.comap (second K R) p ∈ Module.support R N at hn
  rw [← comaps_eq K R p h.2] at hn
  have he : PrimeSpectrum.comap (DiagonalTensorNaturality.first K R) p = IsLocalRing.closedPoint R := Set.mem_singleton_iff.mp (hp ⟨hm, hn⟩)
  have hpoint := SplitSurjectiveSpectrum.comap R (DiagonalTensor.Ring K R) (DiagonalTensor.multiplication K R) (DiagonalTensorNaturality.first K R)
    (first_section K R) p (kernel_le K R p h.2)
  rw [he] at hpoint
  exact Set.mem_singleton_iff.mpr hpoint.symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalSupport
