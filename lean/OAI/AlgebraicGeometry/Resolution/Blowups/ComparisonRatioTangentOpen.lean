import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.TangentComparisonCongruence

/-! # Comparison Ratio Tangent Open -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ComparisonRatioTangentOpen.Construction

noncomputable section

/-! Exceptional parameters differing by a tangent section define common blowup charts around every transformed order point. -/

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem blowupChartRatio_sub_one_mem_transformed_tangent
    (k : Type*) [CommRing k] {R : Type*} [CommRing R] [Algebra k R]
    (I J : Ideal R) (a b : I) (n : ℕ) (hp : J ≤ I ^ (n + 1))
    (hab : b.val - a.val ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) :
    ExceptionalIdeal.Construction.blowupChartRatio I a b - 1 ∈
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) n := by
  let T := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n
  let α := Blowup.Charts.Construction.blowupChartConstants I a a.val
  have hT : T ≤ I ^ 1 := by
    simpa only [pow_one] using Blowups.Ideal.ImageCongruence.Construction.relative_tangent_le_permissible_center k J I n hp
  obtain ⟨d, hd, he⟩ := DifferentialIdealTransform.Construction.blowup_controlledTransform_section_exists I T a 1 hT ⟨b.val - a.val, hab⟩
  have he' : Blowup.Charts.Construction.blowupChartConstants I a (b.val - a.val) = α * d :=
    he.trans (congrArg (fun c : Blowup.Charts.Construction.blowupChart I a => c * d) (pow_one α))
  have hr : ExceptionalIdeal.Construction.blowupChartRatio I a b - 1 = d := by
    apply (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a).left
    calc
      α * (ExceptionalIdeal.Construction.blowupChartRatio I a b - 1) = Blowup.Charts.Construction.blowupChartConstants I a b.val - α := by
        exact (mul_sub α (ExceptionalIdeal.Construction.blowupChartRatio I a b) 1).trans
          (congrArg₂ (fun x y : Blowup.Charts.Construction.blowupChart I a => x - y) (ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio I a b) (mul_one α))
      _ = Blowup.Charts.Construction.blowupChartConstants I a (b.val - a.val) := (map_sub (Blowup.Charts.Construction.blowupChartConstants I a) _ _).symm
      _ = α * d := he'
  have hinc : ControlledTransform.Construction.blowupControlledTransform I T 1 a ≤
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) n := by
    simpa only [Nat.add_comm 1 n] using Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_controlledTransform_le k I J a 1 n
      (by simpa only [Nat.add_comm 1 n] using hp)
  exact hr ▸ hinc hd

theorem blowupChartRatio_not_mem_transformed_order_prime
    (k : Type*) [CommRing k] {R : Type*} [CommRing R] [Algebra k R]
    (I J : Ideal R) (a b : I) (n : ℕ) (hp : J ≤ I ^ (n + 1))
    (hab : b.val - a.val ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (P : PrimeSpectrum (Blowup.Charts.Construction.blowupChart I a))
    (hP : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) n ≤ P.asIdeal) :
    ExceptionalIdeal.Construction.blowupChartRatio I a b ∉ P.asIdeal := by
  intro hu
  have hd := hP (blowupChartRatio_sub_one_mem_transformed_tangent k I J a b n hp hab)
  have hone : (1 : Blowup.Charts.Construction.blowupChart I a) ∈ P.asIdeal := by
    exact (sub_sub_cancel (ExceptionalIdeal.Construction.blowupChartRatio I a b) 1) ▸ P.asIdeal.sub_mem hu hd
  exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ComparisonRatioTangentOpen.Construction
