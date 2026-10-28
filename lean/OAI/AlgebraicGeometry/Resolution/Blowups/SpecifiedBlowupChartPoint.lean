import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartSpecifiedMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialMap

/-! # Specified Blowup Chart Point -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.SpecifiedBlowupChartPoint.Construction

noncomputable section

/-! Lift order points through the actual chart base-change square with independently named target data. -/

universe u

theorem exists_blowupChartMapTo_prime
    {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (a : I) (f : R →+* S) (hf : f.Etale)
    (K : Ideal S) (hK : I.map f = K) (b : K) (hb : b.val = f a.val)
    (p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart I a)) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants I a) p) :
    ∃ Q : PrimeSpectrum (Blowup.Charts.Construction.blowupChart K b),
      PrimeSpectrum.comap (Blowup.ChartSpecifiedMap.Construction.blowupChartMapTo I a f K hK b hb) Q = p ∧
        PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants K b) Q = q := by
  subst K
  have he : b = ⟨f a.val, Ideal.mem_map_of_mem f a.property⟩ := Subtype.ext hb
  subst b
  exact Blowup.ChartOpenBaseChange.Construction.exists_blowupChartMap_prime I a f hf p q hq

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem blowupChartMapTo_transformed_order_prime
    (k : Type u) [CommRing k] {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (I J : Ideal R) (a : I) [Algebra.Smooth k (Blowup.Charts.Construction.blowupChart I a)]
    (n : ℕ) (hp : J ≤ I ^ (n + 1)) (f : R →ₐ[k] S) (hf : f.toRingHom.Etale)
    (K : Ideal S) (hK : I.map f.toRingHom = K) (b : K) (hb : b.val = f a.val)
    (p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart I a)) (Q : PrimeSpectrum (Blowup.Charts.Construction.blowupChart K b))
    (hQ : PrimeSpectrum.comap (Blowup.ChartSpecifiedMap.Construction.blowupChartMapTo I a f.toRingHom K hK b hb) Q = p)
    (hporder : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) n ≤ p.asIdeal) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (ControlledTransform.Construction.blowupControlledTransform K (J.map f.toRingHom) (n + 1) b) n ≤ Q.asIdeal := by
  let F := Blowup.ChartSpecifiedMap.Construction.blowupChartMapToAlgHom k I a f K hK b hb
  have hn := Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k F
    (Blowup.ChartSpecifiedMap.Construction.blowupChartMapTo_etale I a f.toRingHom hf K hK b hb)
    (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) n
  change (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) n).map
      (Blowup.ChartSpecifiedMap.Construction.blowupChartMapTo I a f.toRingHom K hK b hb) =
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k ((ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a).map
      (Blowup.ChartSpecifiedMap.Construction.blowupChartMapTo I a f.toRingHom K hK b hb)) n at hn
  rw [Blowup.ChartSpecifiedMap.Construction.blowupChartMapTo_controlledIdeal I J a f.toRingHom K hK b hb (n + 1) hp] at hn
  rw [← hn]
  apply Ideal.map_le_iff_le_comap.mpr
  exact hporder.trans_eq (congrArg PrimeSpectrum.asIdeal hQ).symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.SpecifiedBlowupChartPoint.Construction
