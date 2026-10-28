import OAI.AlgebraicGeometry.Resolution.Blowups.CommonBlowupChartMaps
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.CenterPreservingComparison

/-! # Common Blowup Tangent Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.CommonBlowupTangentComparison.Construction

noncomputable section

/-! Tangent congruence and every later permissible center agree under the constructed common-chart maps. -/

universe u

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra Blowup.Overlap.Construction.blowupOverlapBaseAlgebra

theorem commonBlowupChart_tangent_comparison
    (k : Type u) [CommRing k] {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (I J : Ideal R) (a : I) (n : ℕ) (hp : J ≤ I ^ (n + 1))
    (f g : R →ₐ[k] S) (K : Ideal S) (hKf : I.map f.toRingHom = K) (hKg : I.map g.toRingHom = K)
    (b c : K) (hb : b.val = f a.val) (hc : c.val = g a.val)
    (hT : (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map f.toRingHom =
      (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map g.toRingHom)
    (hdiff : ∀ r : R, g r - f r ∈ (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map f.toRingHom) :
    let F := CommonBlowupChartMaps.Construction.commonBlowupChartLeft k I a f K hKf b c hb
    let G := CommonBlowupChartMaps.Construction.commonBlowupChartRight k I a g K hKg b c hc
    let T' := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) n
    T'.map F.toRingHom = T'.map G.toRingHom ∧
      (∀ x : Blowup.Charts.Construction.blowupChart I a, G x - F x ∈ T'.map F.toRingHom) ∧
      ∀ L : Ideal (Blowup.Charts.Construction.blowupChart I a), ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a ≤ L ^ (n + 1) →
        L.map F.toRingHom = L.map G.toRingHom := by
  let F := CommonBlowupChartMaps.Construction.commonBlowupChartLeft k I a f K hKf b c hb
  let G := CommonBlowupChartMaps.Construction.commonBlowupChartRight k I a g K hKg b c hc
  let q := Blowup.ChartOverlap.Construction.blowupChartOverlapConstants K b c
  have hF : F.toRingHom.comp (Blowup.Charts.Construction.blowupChartConstants I a) = q.comp f.toRingHom := by
    apply RingHom.ext
    intro r
    exact CommonBlowupChartMaps.Construction.commonBlowupChartLeft_constants k I a f K hKf b c hb r
  have hG : G.toRingHom.comp (Blowup.Charts.Construction.blowupChartConstants I a) = q.comp g.toRingHom := by
    apply RingHom.ext
    intro r
    exact CommonBlowupChartMaps.Construction.commonBlowupChartRight_constants k I a g K hKg b c hc r
  obtain ⟨hreg, u, hu⟩ := CommonBlowupChartMaps.Construction.commonBlowupChart_parameters k I a f g K hKf hKg b c hb hc
  apply Blowup.CenterPreservingComparison.Construction.blowupChart_center_preserving_comparison k I J a n hp F.toRingHom G.toRingHom hreg u hu
  · rw [hF, hG, ← Ideal.map_map, ← Ideal.map_map, hT]
  · intro r
    change G (Blowup.Charts.Construction.blowupChartConstants I a r) - F (Blowup.Charts.Construction.blowupChartConstants I a r) ∈ _
    rw [CommonBlowupChartMaps.Construction.commonBlowupChartLeft_constants, CommonBlowupChartMaps.Construction.commonBlowupChartRight_constants, hF, ← Ideal.map_map]
    exact (map_sub q (g r) (f r)) ▸ Ideal.mem_map_of_mem q (hdiff r)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.CommonBlowupTangentComparison.Construction
