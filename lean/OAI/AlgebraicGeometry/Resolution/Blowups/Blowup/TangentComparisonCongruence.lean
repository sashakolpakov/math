import OAI.AlgebraicGeometry.Resolution.Blowups.DividedComparisonCongruence
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.Ideal.ImageCongruence

/-! # Tangent Comparison Congruence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.TangentComparisonCongruence.Construction

noncomputable section

/-! Congruence modulo the original tangent ideal passes to the transformed tangent ideal on common blowup charts. -/

universe u v

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem blowupChart_tangent_congruence
    (k : Type*) [CommRing k] {R : Type u} [CommRing R] [Algebra k R]
    {S : Type v} [CommRing S] (I J : Ideal R) (a : I) (n : ℕ) (hp : J ≤ I ^ (n + 1))
    (f g : Charts.Construction.blowupChart I a →+* S)
    (hregular : IsRegular (f (Charts.Construction.blowupChartConstants I a a.val)))
    (u : Sˣ) (hu : g (Charts.Construction.blowupChartConstants I a a.val) = f (Charts.Construction.blowupChartConstants I a a.val) * u)
    (hdiff : ∀ r : R, g (Charts.Construction.blowupChartConstants I a r) - f (Charts.Construction.blowupChartConstants I a r) ∈
      (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map (f.comp (Charts.Construction.blowupChartConstants I a))) :
    ∀ x : Charts.Construction.blowupChart I a, g x - f x ∈
      (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) n).map f := by
  let T := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n
  let T' := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) n
  have hT : T ≤ I ^ 1 := by
    simpa only [pow_one] using Blowups.Ideal.ImageCongruence.Construction.relative_tangent_le_permissible_center k J I n hp
  have hfactor : T.map (Charts.Construction.blowupChartConstants I a) =
      Ideal.span {Charts.Construction.blowupChartConstants I a a.val} * ControlledTransform.Construction.blowupControlledTransform I T 1 a := by
    have he := (ControlledTransform.Construction.blowup_controlledTransform_factorization I T 1 a hT).symm
    exact he.trans (congrArg (fun c : Charts.Construction.blowupChart I a => Ideal.span {c} * ControlledTransform.Construction.blowupControlledTransform I T 1 a)
      (pow_one (Charts.Construction.blowupChartConstants I a a.val)))
  have hinc : ControlledTransform.Construction.blowupControlledTransform I T 1 a ≤ T' := by
    simpa only [Nat.add_comm 1 n] using Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_controlledTransform_le k I J a 1 n
      (by simpa only [Nat.add_comm 1 n] using hp)
  have htotal : T.map (f.comp (Charts.Construction.blowupChartConstants I a)) ≤
      Ideal.span {f (Charts.Construction.blowupChartConstants I a a.val)} * T'.map f := by
    rw [← Ideal.map_map, hfactor, Ideal.map_mul, Ideal.map_span, Set.image_singleton]
    exact Ideal.mul_mono le_rfl (Ideal.map_mono hinc)
  apply DividedComparisonCongruence.Construction.blowupChart_congruence_of_divided_constants I a f g (T'.map f) hregular u hu
  intro r
  obtain ⟨d, hd, he⟩ := Ideal.mem_span_singleton_mul.mp (htotal (hdiff r))
  exact ⟨d, hd, he.symm⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.TangentComparisonCongruence.Construction
