import OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalRingAvoidance
import OAI.RepresentationTheory.Theta.Adelic.QuadraticOrderLift

/-! # Integral Spectral Avoidance -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntegralSpectralAvoidance

noncomputable section

/-! A finite scalar family with integral unit differences moves any
integral quadratic matrix into an open cell with integral inverse. -/

open scoped Classical

open OAI.RepresentationTheory.Theta.Adelic.QuadraticIntegralCoefficients OAI.RepresentationTheory.Theta.Adelic.QuadraticOrderLift
open OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalRingAvoidance

variable {k I J : Type*} [Field k] [Fintype I] [Fintype J] [DecidableEq J]
variable (S : Subring k) [IsLocalRing S] (d : k) (hd : d ∈ S)

theorem integral_spectral_avoidance (A : Matrix J J (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))
    (hA : ∀ i j, A i j ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd) (z : I → Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)
    (hz : ∀ i, z i ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd)
    (hdiff : ∀ i j, i ≠ j → ∃ u : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ, u.val = z i - z j ∧
      u.val ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd ∧ u.inv ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd)
    (hcard : 2 * Fintype.card J < Fintype.card I) :
    ∃ i, ∃ u : (Matrix J J (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ, u.val = Matrix.scalar J (z i) - A ∧
      (∀ i j, u.val i j ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd) ∧
      (∀ i j, u.inv i j ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd) := by
  let f := Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange S.subtype (⟨d, hd⟩ : S)
  have hf : Function.Injective f := by
    intro x y h
    exact QuadraticAlgebra.ext (Subtype.ext (congrArg QuadraticAlgebra.re h))
      (Subtype.ext (congrArg QuadraticAlgebra.im h))
  let A' : Matrix J J (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic S (⟨d, hd⟩ : S)) := fun i j => QuadraticOrderLift.integralElement S d hd (A i j) (hA i j)
  let z' : I → Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic S (⟨d, hd⟩ : S) := fun i => QuadraticOrderLift.integralElement S d hd (z i) (hz i)
  have hzmap (i : I) : f (z' i) = z i := QuadraticOrderLift.integralElement_map S d hd _ _
  have hAmap : A'.map f = A := by
    apply Matrix.ext
    intro i j
    exact QuadraticOrderLift.integralElement_map S d hd _ _
  have hdu : ∀ i j, i ≠ j → IsUnit (z' i - z' j) := by
    intro i j hij
    obtain ⟨u, hu, hv, hi⟩ := hdiff i j hij
    have he : (QuadraticOrderLift.integralUnit S d hd u hv hi).val = z' i - z' j := by
      apply hf
      have hmap := congrArg Units.val (QuadraticOrderLift.integralUnit_map S d hd u hv hi)
      change f (QuadraticOrderLift.integralUnit S d hd u hv hi).val = u.val at hmap
      rw [hmap, map_sub, hzmap, hzmap, hu]
      rfl
    exact he ▸ (QuadraticOrderLift.integralUnit S d hd u hv hi).isUnit
  obtain ⟨i, hi⟩ := QuadraticLocalRingAvoidance.quadratic_local_ring_avoidance (⟨d, hd⟩ : S) A' z' hdu hcard
  let u' := hi.unit
  let u : (Matrix J J (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ := Units.map f.mapMatrix.toMonoidHom u'
  refine ⟨i, u, ?_, ?_, ?_⟩
  · change u'.val.map f = Matrix.scalar J (z i) - A
    rw [show u'.val = Matrix.scalar J (z' i) - A' from hi.unit_spec]
    rw [← hAmap, ← hzmap i]
    apply Matrix.ext
    intro j l
    by_cases h : j = l <;> simp [Matrix.map_apply, Matrix.scalar_apply, h]
    · exact f.map_sub _ _
    · exact f.map_neg _
  · intro j l
    exact (QuadraticOrderLift.orderMap S d hd (u'.val j l)).property
  · intro j l
    exact (QuadraticOrderLift.orderMap S d hd (u'.inv j l)).property

end

end OAI.RepresentationTheory.Theta.Adelic.IntegralSpectralAvoidance
