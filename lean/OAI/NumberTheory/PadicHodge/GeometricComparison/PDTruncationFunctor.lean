import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # PD Truncation Functor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PDTruncationFunctor.PDTruncationMap

noncomputable section

/-! Actual divided-power truncations are functorial in divided-power ring maps,
with their inherited divided powers. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation

universe u v w
variable {A : Type u} [CommRing A] {I : Ideal A} {δ : DividedPowers I}
  {B : Type v} [CommRing B] {J : Ideal B} {ε : DividedPowers J}
  (f : DividedPowers.DPMorphism δ ε) (n : ℕ)

def map : AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.Ring A I n →+* AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.Ring B J n :=
  Ideal.quotientMap (J ^ (n + 1)) f.toRingHom (by
    apply Ideal.map_le_iff_le_comap.mp
    rw [Ideal.map_pow]
    exact pow_le_pow_left' f.ideal_comp (n + 1))

theorem map_quotient : (map f n).comp (Ideal.Quotient.mk (I ^ (n + 1))) =
    (Ideal.Quotient.mk (J ^ (n + 1))).comp f.toRingHom := by
  apply RingHom.ext
  intro a
  rfl

theorem isDPMorphism : DividedPowers.IsDPMorphism
    (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.dividedPowers A I δ n) (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.dividedPowers B J ε n) (map f n) := by
  apply DividedPowers.IsDPMorphism.of_comp δ (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.dividedPowers A I δ n) (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.dividedPowers B J ε n)
    (Ideal.Quotient.mk (I ^ (n + 1))) (map f n) rfl (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.quotient_isDPMorphism A I δ n)
  rw [map_quotient]
  exact (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.quotient_isDPMorphism B J ε n).comp _ f.isDPMorphism

def dpMap : DividedPowers.DPMorphism (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.dividedPowers A I δ n) (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.dividedPowers B J ε n) where
  toRingHom := map f n
  ideal_comp := (PDTruncationMap.isDPMorphism f n).ideal_comp
  dpow_comp := (PDTruncationMap.isDPMorphism f n).dpow_comp

variable {C : Type w} [CommRing C] {L : Ideal C} {ζ : DividedPowers L}
  (g : DividedPowers.DPMorphism ε ζ)

theorem map_comp : (map g n).comp (map f n) = map (g.comp f) n := by
  apply RingHom.ext
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PDTruncationFunctor.PDTruncationMap
