import OAI.Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothLocalDomain

/-! # Smooth Local -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothLocal.Constructions.SmoothLocalKernel

noncomputable section

/-! # RiemannProjectivity: a dominant algebraic quotient of a smooth algebra has zero local kernel -/

variable {R A D : Type*} [CommRing R] [IsDomain R] [CommRing A] [CommRing D] [IsDomain D]
  [Algebra R A] [Algebra R D] [Algebra.IsAlgebraic R A]

theorem kernel_vanishes (f : A →ₐ[R] D)
    (hinj : Function.Injective (algebraMap R D)) (p : Ideal A) [p.IsPrime]
    (hp : RingHom.ker f.toRingHom ≤ p) [IsDomain (Localization.AtPrime p)]
    (a : A) (ha : f a = 0) :
    algebraMap A (Localization.AtPrime p) a = 0 := by
  let K := FractionRing D
  let B := Localization.AtPrime p
  let g : A →ₐ[R] K := (Algebra.algHom R D K).comp f
  have hg (s : p.primeCompl) : IsUnit (g s) := by
    apply isUnit_iff_ne_zero.mpr
    change algebraMap D K (f s.val) ≠ 0
    intro hs
    have hfzero : f s.val = 0 := (IsFractionRing.injective D K) (hs.trans (map_zero _).symm)
    exact s.property (hp hfzero)
  let l : B →ₐ[R] K := IsLocalization.liftAlgHom (S := B) hg
  have hl : Function.Injective l := by
    let : Algebra.IsAlgebraic R B := JacobianLocalizationAt.Constructions.AlgebraicLocalization.isAlgebraic p.primeCompl
    let : Algebra B K := l.toRingHom.toAlgebra
    let : IsScalarTower R B K := IsScalarTower.of_algebraMap_eq' l.comp_algebraMap.symm
    change Function.Injective (algebraMap B K)
    apply Algebra.IsAlgebraic.injective_tower_top (R := R) B
    exact (IsFractionRing.injective D K).comp hinj
  apply hl
  change IsLocalization.lift hg (algebraMap A B a) = l 0
  rw [IsLocalization.lift_eq, map_zero]
  change algebraMap D K (f a) = 0
  rw [ha, map_zero]

theorem kernel_vanishes_of_smooth [Algebra ℂ A] [Algebra.Smooth ℂ A]
    (f : A →ₐ[R] D) (hinj : Function.Injective (algebraMap R D))
    (p : Ideal A) [p.IsPrime] (hp : RingHom.ker f.toRingHom ≤ p)
    (a : A) (ha : f a = 0) :
    algebraMap A (Localization.AtPrime p) a = 0 := by
  let : IsDomain (Localization.AtPrime p) := AlgebraicGeometry.Foundations.Scheme.SmoothLocalDomain.isDomain_localizationAtPrime_of_smooth ℂ A p
  exact kernel_vanishes f hinj p hp a ha

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothLocal.Constructions.SmoothLocalKernel
