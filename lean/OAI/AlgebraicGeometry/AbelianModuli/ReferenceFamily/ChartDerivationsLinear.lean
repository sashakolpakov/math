import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.AffineDualChart

/-! # Chart Derivations Linear -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChartDerivationsLinear

noncomputable section

section

/-! The genuine chart-to-dual-point comparison is complex linear when
the target carries its intrinsic derivation vector space. -/

variable {S U : Type*} [CommRing S] [Algebra ℂ S] [NormedAddCommGroup U] [NormedSpace ℂ U]

def chartDerivationsLinearEquiv (φ : U → Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (u : U)
    (d : U ≃ Dual.PresentedAlgebra.DualAlgebraPoints (φ u))
    (hd : ∀ v a, ((d v).val a).snd = fderiv ℂ (fun w => φ w a) u v) :
    U ≃ₗ[ℂ] PointDerivations.pointDerivations (φ u) where
  toEquiv := d.trans (PointDerivations.dualPointDerivationsEquiv (φ u))
  map_add' v w := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    change ((d (v + w)).val a).snd = ((d v).val a).snd + ((d w).val a).snd
    rw [hd, hd, hd, map_add]
  map_smul' c v := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    change ((d (c • v)).val a).snd = c • ((d v).val a).snd
    rw [hd, hd, map_smul]

theorem chartDerivationsLinearEquiv_apply (φ : U → Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (u : U)
    (d : U ≃ Dual.PresentedAlgebra.DualAlgebraPoints (φ u))
    (hd : ∀ v a, ((d v).val a).snd = fderiv ℂ (fun w => φ w a) u v) (v : U) (a : S) :
    (chartDerivationsLinearEquiv φ u d hd v).val a = fderiv ℂ (fun w => φ w a) u v := hd v a

end

/-! Reindexing genuine chart coordinates transports the constructed
derivation comparison by the actual linear coordinate isomorphism. -/

open scoped ContDiff _root_.Topology

variable {S U V : Type*} [CommRing S] [Algebra ℂ S]
  [NormedAddCommGroup U] [NormedSpace ℂ U] [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem reindexChart_derivations
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) U) (b : U ≃L[ℂ] V)
    (hreg : ∀ a : S, ContDiffOn ℂ ω (fun u => e.symm u a) e.target)
    (hd : ∀ u ∈ e.target, ∃ d : U ≃ₗ[ℂ] PointDerivations.pointDerivations (e.symm u),
      ∀ v a, (d v).val a = fderiv ℂ (fun w => e.symm w a) u v) :
    ∀ u ∈ (e.transHomeomorph b.toHomeomorph).target,
      ∃ d : V ≃ₗ[ℂ] PointDerivations.pointDerivations ((e.transHomeomorph b.toHomeomorph).symm u),
        ∀ v a, (d v).val a = fderiv ℂ (fun w => (e.transHomeomorph b.toHomeomorph).symm w a) u v := by
  intro u hu
  have hub : b.symm u ∈ e.target := hu
  obtain ⟨d0, hd0⟩ := hd (b.symm u) hub
  refine ⟨b.symm.toLinearEquiv.trans d0, ?_⟩
  intro v a
  have hdiff := ((hreg a).contDiffAt (e.open_target.mem_nhds hub)).differentiableAt
    (show (ω : ℕ∞ω) ≠ 0 by simp)
  have hc := hdiff.hasFDerivAt.comp u b.symm.hasFDerivAt
  exact (hd0 (b.symm v) a).trans (DFunLike.congr_fun hc.fderiv v).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChartDerivationsLinear
