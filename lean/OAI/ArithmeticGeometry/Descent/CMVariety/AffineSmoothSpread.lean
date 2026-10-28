import OAI.ArithmeticGeometry.Descent.CMVariety.GenericSmoothNeighborhood
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.Algebra.Rat

/-! # Affine Smooth Spread -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.AffineSmoothSpread.Abelian

noncomputable section

/-!
A point of an affine finite-type rational scheme factors through a smooth
integral rational scheme with a monomorphism to the original scheme. The
construction takes the actual kernel of its complex evaluation and then
the smooth open locus at the resulting arithmetic generic point.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {A : Type} [CommRing A] [Algebra ℚ A] [Algebra.FiniteType ℚ A]

theorem affine_complex_point_has_smooth_arithmetic_factor (x : A →ₐ[ℚ] ℂ) :
    ∃ (Y : Scheme) (f : Y ⟶ Spec (CommRingCat.of ℚ))
      (i : Y ⟶ Spec (CommRingCat.of A)) (q : Spec (CommRingCat.of ℂ) ⟶ Y),
      IsIntegral Y ∧ Smooth f ∧ Mono i ∧
      i ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ A)) = f ∧
      q ≫ i = Spec.map (CommRingCat.ofHom x.toRingHom) := by
  let I := RingHom.ker x
  let B := A ⧸ I
  let : I.IsPrime := RingHom.ker_isPrime x
  let φ : B →ₐ[ℚ] ℂ := Ideal.kerLiftAlg x
  have hφ : Function.Injective φ := Ideal.kerLiftAlg_injective x
  let fB := Spec.map (CommRingCat.ofHom (algebraMap ℚ B))
  let p := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let j := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let : Algebra.FinitePresentation ℚ B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : LocallyOfFinitePresentation fB :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have hp : p (IsLocalRing.closedPoint ℂ) = genericPoint (Spec (CommRingCat.of B)) := by
    rw [genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    change Ideal.comap φ.toRingHom (IsLocalRing.maximalIdeal ℂ) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact (RingHom.injective_iff_ker_eq_bot φ.toRingHom).mp hφ
  obtain ⟨U, hU, hSmooth, q, hq⟩ := GenericSmoothNeighborhood.Abelian.generic_complex_point_factors_through_smooth_open fB p hp
  let : IsIntegral U := hU
  let : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk I)) Ideal.Quotient.mk_surjective
  have hj : j ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ A)) = fB := by
    rw [← Spec.map_comp]
    rfl
  have hx : p ≫ j = Spec.map (CommRingCat.ofHom x.toRingHom) := by
    rw [← Spec.map_comp]
    rfl
  refine ⟨U, U.ι ≫ fB, U.ι ≫ j, q, hU, hSmooth, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, hj]
  · rw [← Category.assoc, hq, hx]

end

end OAI.ArithmeticGeometry.Descent.CMVariety.AffineSmoothSpread.Abelian
