import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-! # Local Fiber -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.LocalFiber

noncomputable section

/-! Smooth fibers have actual local domain rings. This supplies reduced
closed fibers for the flat comparison of native orders of vanishing. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

theorem geometricallyReduced {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] :
    GeometricallyReduced f := by
  constructor
  intro K _ y Z fst snd h
  let : Smooth snd := MorphismProperty.of_isPullback h (inferInstance : Smooth f)
  exact Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced snd

theorem localization_domain (K A S : Type u) [Field K] [CommRing A] [Algebra K A]
    [Algebra.Smooth K A] [CommRing S] [IsLocalRing S] [Algebra A S]
    (M : Submonoid A) [IsLocalization M S] : IsDomain S := by
  let p := (IsLocalRing.maximalIdeal S).comap (algebraMap A S)
  let : p.IsPrime := Ideal.IsPrime.comap _
  have hm : M ≤ p.primeCompl := by
    intro a ha
    exact (IsLocalRing.notMem_maximalIdeal.mpr (IsLocalization.map_units S (⟨a, ha⟩ : M)))
  let : IsLocalization.AtPrime S p := IsLocalization.of_le M p.primeCompl hm
    (fun a ha => IsLocalRing.notMem_maximalIdeal.mp ha)
  exact Foundations.Scheme.SmoothLocalDomain.isDomain_of_isLocalizationAtPrime_of_smooth K A S p

theorem fiber_domain (R A S : Type u) [CommRing R] [IsLocalRing R]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A]
    [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra A S] [IsScalarTower R A S] (M : Submonoid A) [IsLocalization M S] :
    IsDomain (IsLocalRing.ResidueField R ⊗[R] S) := by
  let K := IsLocalRing.ResidueField R
  let B := K ⊗[R] A
  let F := K ⊗[R] S
  let φ : B →ₐ[K] F := Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom R A S)
  let : Algebra B F := φ.toRingHom.toAlgebra
  let : IsScalarTower K B F := IsScalarTower.of_algebraMap_eq' (by
    ext k
    exact (φ.commutes k).symm)
  let : IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := R) (A := K))) F :=
    IsLocalization.tensorProduct_tensorProduct_right R K M S (by
      ext a
      simp only [RingHom.comp_apply]
      change φ (1 ⊗ₜ[R] a) = 1 ⊗ₜ[R] algebraMap A S a
      exact Algebra.TensorProduct.map_tmul (AlgHom.id K K) (IsScalarTower.toAlgHom R A S) 1 a)
  exact localization_domain K B F (M.map (Algebra.TensorProduct.includeRight (R := R) (A := K)))

theorem quotient_domain (R A S : Type u) [CommRing R] [IsLocalRing R]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A]
    [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra A S] [IsScalarTower R A S] (M : Submonoid A) [IsLocalization M S] :
    IsDomain (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) := by
  let : IsDomain (IsLocalRing.ResidueField R ⊗[R] S) := fiber_domain R A S M
  let e : IsLocalRing.ResidueField R ⊗[R] S ≃ₐ[R]
      S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S) :=
    (Algebra.TensorProduct.comm R _ S).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (IsLocalRing.maximalIdeal R)).symm.restrictScalars R)
  exact e.symm.injective.isDomain e.symm.toRingHom

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.LocalFiber
