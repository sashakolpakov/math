import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartSpecifiedMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Overlap

/-! # Common Blowup Chart Maps -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.CommonBlowupChartMaps.Construction

noncomputable section

/-! Two actual maps from one blowup chart into the overlap of the corresponding target charts. -/

universe u

variable (k : Type u) [CommRing k] {R S : Type u} [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra Blowup.Overlap.Construction.blowupOverlapBaseAlgebra

def commonBlowupChartLeft (I : Ideal R) (a : I) (f : R →ₐ[k] S)
    (K : Ideal S) (hK : I.map f.toRingHom = K) (b c : K) (hb : b.val = f a.val) :
    Blowup.Charts.Construction.blowupChart I a →ₐ[k] Blowup.ChartOverlap.Construction.blowupChartOverlap K b c :=
  (Blowup.Overlap.Construction.blowupChartOverlapLeftAlgHom K b c k).comp (Blowup.ChartSpecifiedMap.Construction.blowupChartMapToAlgHom k I a f K hK b hb)

def commonBlowupChartRight (I : Ideal R) (a : I) (g : R →ₐ[k] S)
    (K : Ideal S) (hK : I.map g.toRingHom = K) (b c : K) (hc : c.val = g a.val) :
    Blowup.Charts.Construction.blowupChart I a →ₐ[k] Blowup.ChartOverlap.Construction.blowupChartOverlap K b c :=
  (Blowup.Overlap.Construction.blowupChartOverlapRightAlgHom K b c k).comp (Blowup.ChartSpecifiedMap.Construction.blowupChartMapToAlgHom k I a g K hK c hc)

theorem commonBlowupChartLeft_constants (I : Ideal R) (a : I) (f : R →ₐ[k] S)
    (K : Ideal S) (hK : I.map f.toRingHom = K) (b c : K) (hb : b.val = f a.val) (r : R) :
    commonBlowupChartLeft k I a f K hK b c hb (Blowup.Charts.Construction.blowupChartConstants I a r) =
      Blowup.ChartOverlap.Construction.blowupChartOverlapConstants K b c (f r) := by
  change Blowup.ChartOverlap.Construction.blowupChartOverlapLeft K b c
    (Blowup.ChartSpecifiedMap.Construction.blowupChartMapTo I a f.toRingHom K hK b hb (Blowup.Charts.Construction.blowupChartConstants I a r)) = _
  rw [Blowup.ChartSpecifiedMap.Construction.blowupChartMapTo_constants, Blowup.ChartOverlap.Construction.blowupChartOverlapLeft_constants]
  rfl

theorem commonBlowupChartRight_constants (I : Ideal R) (a : I) (g : R →ₐ[k] S)
    (K : Ideal S) (hK : I.map g.toRingHom = K) (b c : K) (hc : c.val = g a.val) (r : R) :
    commonBlowupChartRight k I a g K hK b c hc (Blowup.Charts.Construction.blowupChartConstants I a r) =
      Blowup.ChartOverlap.Construction.blowupChartOverlapConstants K b c (g r) := by
  change Blowup.ChartOverlap.Construction.blowupChartOverlapRight K b c
    (Blowup.ChartSpecifiedMap.Construction.blowupChartMapTo I a g.toRingHom K hK c hc (Blowup.Charts.Construction.blowupChartConstants I a r)) = _
  rw [Blowup.ChartSpecifiedMap.Construction.blowupChartMapTo_constants, Blowup.ChartOverlap.Construction.blowupChartOverlapRight_constants]
  rfl

theorem commonBlowupChartLeft_etale (I : Ideal R) (a : I) (f : R →ₐ[k] S)
    (hf : f.toRingHom.Etale) (K : Ideal S) (hK : I.map f.toRingHom = K)
    (b c : K) (hb : b.val = f a.val) :
    (commonBlowupChartLeft k I a f K hK b c hb).toRingHom.Etale :=
  RingHom.Etale.stableUnderComposition _ _ (Blowup.ChartSpecifiedMap.Construction.blowupChartMapTo_etale I a f.toRingHom hf K hK b hb)
    (Blowup.Overlap.Construction.blowupChartOverlapLeft_etale K b c)

theorem commonBlowupChartRight_etale (I : Ideal R) (a : I) (g : R →ₐ[k] S)
    (hg : g.toRingHom.Etale) (K : Ideal S) (hK : I.map g.toRingHom = K)
    (b c : K) (hc : c.val = g a.val) :
    (commonBlowupChartRight k I a g K hK b c hc).toRingHom.Etale :=
  RingHom.Etale.stableUnderComposition _ _ (Blowup.ChartSpecifiedMap.Construction.blowupChartMapTo_etale I a g.toRingHom hg K hK c hc)
    (Blowup.Overlap.Construction.blowupChartOverlapRight_etale K b c)

theorem commonBlowupChart_parameters (I : Ideal R) (a : I) (f g : R →ₐ[k] S)
    (K : Ideal S) (hKf : I.map f.toRingHom = K) (hKg : I.map g.toRingHom = K)
    (b c : K) (hb : b.val = f a.val) (hc : c.val = g a.val) :
    let F := commonBlowupChartLeft k I a f K hKf b c hb
    let G := commonBlowupChartRight k I a g K hKg b c hc
    IsRegular (F (Blowup.Charts.Construction.blowupChartConstants I a a.val)) ∧
      ∃ u : (Blowup.ChartOverlap.Construction.blowupChartOverlap K b c)ˣ,
        G (Blowup.Charts.Construction.blowupChartConstants I a a.val) = F (Blowup.Charts.Construction.blowupChartConstants I a a.val) * u := by
  dsimp only
  rw [commonBlowupChartLeft_constants, commonBlowupChartRight_constants, ← hb, ← hc]
  refine ⟨Blowup.OverlapTransitions.Construction.blowupChartOverlapLeft_parameter_regular K b c, ?_⟩
  obtain ⟨u, hu⟩ := Blowup.OverlapTransitions.Construction.blowupChartOverlapLeft_ratio_isUnit K b c
  refine ⟨u, ?_⟩
  rw [hu]
  exact (Blowup.OverlapTransitions.Construction.blowupChartOverlapLeft_factorization K b c c).symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.CommonBlowupChartMaps.Construction
