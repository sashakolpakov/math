import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Localization Spectrum -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.LocalizationSpectrum

noncomputable section

/-! Localizing either factor of an affine product embeds its prime
spectrum into the original product spectrum, preserving strict prime
inclusions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u

theorem strict_comap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] : StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
  intro p q hpq
  exact (IsLocalization.orderEmbedding M S).strictMono hpq

variable (K A B C : Type u) [CommRing K] [CommRing A] [CommRing B] [CommRing C]
  [Algebra K A] [Algebra K B] [Algebra K C] [Algebra A B] [IsScalarTower K A B]

def leftMap : A ⊗[K] C →+* B ⊗[K] C :=
  (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A B) (AlgHom.id K C)).toRingHom

def rightMap : C ⊗[K] A →+* C ⊗[K] B :=
  (Algebra.TensorProduct.map (AlgHom.id K C) (IsScalarTower.toAlgHom K A B)).toRingHom

theorem left_strict (M : Submonoid A) [IsLocalization M B] :
    StrictMono (PrimeSpectrum.comap (leftMap K A B C)) := by
  let := (leftMap K A B C).toAlgebra
  let : IsScalarTower A (A ⊗[K] C) (B ⊗[K] C) := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A B a ⊗ₜ[K] (1 : C) = algebraMap A B a ⊗ₜ[K] (AlgHom.id K C) 1
    rfl
  let : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[K] C) M) (B ⊗[K] C) :=
    IsLocalization.tensorProduct_tensorProduct K C M B (by
      ext c
      change algebraMap A B 1 ⊗ₜ[K] c = (1 : B) ⊗ₜ[K] c
      rw [map_one])
  exact strict_comap (A ⊗[K] C) (B ⊗[K] C) (Algebra.algebraMapSubmonoid (A ⊗[K] C) M)

theorem right_strict (M : Submonoid A) [IsLocalization M B] :
    StrictMono (PrimeSpectrum.comap (rightMap K A B C)) := by
  let := (rightMap K A B C).toAlgebra
  let : IsScalarTower C (C ⊗[K] A) (C ⊗[K] B) := IsScalarTower.of_algebraMap_eq fun c => by
    change c ⊗ₜ[K] (1 : B) = (AlgHom.id K C) c ⊗ₜ[K] (algebraMap A B) 1
    rw [map_one]
    rfl
  let : IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := K) (A := C))) (C ⊗[K] B) :=
    IsLocalization.tensorProduct_tensorProduct_right K C M B (by ext a; rfl)
  exact strict_comap (C ⊗[K] A) (C ⊗[K] B)
    (M.map (Algebra.TensorProduct.includeRight (R := K) (A := C)))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.LocalizationSpectrum
