import OAI.AlgebraicGeometry.Comparison.Betti.AnnularCauchyFormula
import OAI.AlgebraicGeometry.Comparison.Betti.ParametricCauchyIntegral

/-! # Parametric Positive Laurent -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ParametricPositiveLaurent.Dolbeault

noncomputable section

/-! The actual positive Laurent projection preserves joint holomorphy
over an arbitrary open finite-dimensional complex parameter domain. -/

open _root_.Complex Set _root_.Metric Filter
open scoped _root_.Topology

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]

def positiveLaurentFamily (G : P × ℂ → ℂ) (q : P × ℂ) : ℂ :=
  AnnularCauchyFormula.Dolbeault.positiveLaurentPart (fun w => G (q.1, w)) q.2

omit [FiniteDimensional ℂ P] in
theorem puncturedFamily_slice_holomorphic {G : P × ℂ → ℂ} {S : Set P}
    (hG : DifferentiableOn ℂ G (S ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))) {p : P} (hp : p ∈ S) :
    DifferentiableOn ℂ (fun w => G (p, w)) (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ) :=
  hG.comp ((differentiable_const p).prodMk differentiable_id).differentiableOn
    (fun _ hw => ⟨hp, hw⟩)

omit [FiniteDimensional ℂ P] in
theorem positiveLaurentFamily_eq_contour {G : P × ℂ → ℂ} {S : Set P}
    (hG : DifferentiableOn ℂ G (S ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ)))
    {q : P × ℂ} (hq : q.1 ∈ S) {R : ℝ} (hR : ‖q.2‖ < R) :
    positiveLaurentFamily G q = ParametricCauchyIntegral.Weierstrass.parametricCauchyIntegral G 0 R q :=
  AnnularCauchyFormula.Dolbeault.positiveLaurentPart_eq_contour (puncturedFamily_slice_holomorphic hG hq) hR

theorem positiveLaurentFamily_holomorphic {G : P × ℂ → ℂ} {S : Set P} (hS : IsOpen S)
    (hG : DifferentiableOn ℂ G (S ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))) :
    DifferentiableOn ℂ (positiveLaurentFamily G) (S ×ˢ univ) := by
  intro q hq
  let R := ‖q.2‖ + 1
  have hz : ‖q.2‖ < R := lt_add_one _
  have hR : 0 < R := (norm_nonneg q.2).trans_lt hz
  have hbound : S ×ˢ sphere (0 : ℂ) R ⊆ S ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ) := by
    intro p hp
    refine ⟨hp.1, ?_⟩
    have hn : ‖p.2‖ = R := by simpa only [mem_sphere, dist_zero_right] using hp.2
    exact norm_pos_iff.mp (hn.symm ▸ hR)
  have hd := ParametricCauchyIntegral.Weierstrass.differentiableAt_parametricCauchyIntegral
    (hS.prod PuncturedCauchy.Dolbeault.puncturedComplexOpen.isOpen) hG hS hR.le hbound hq.1
    (show q.2 ∈ ball 0 R by simpa only [mem_ball, dist_zero_right] using hz)
  have he : positiveLaurentFamily G =ᶠ[𝓝 q] ParametricCauchyIntegral.Weierstrass.parametricCauchyIntegral G 0 R := by
    filter_upwards [(hS.prod isOpen_ball).mem_nhds
      (show q ∈ S ×ˢ ball (0 : ℂ) R from ⟨hq.1, by simpa only [mem_ball, dist_zero_right] using hz⟩)]
      with p hp
    exact positiveLaurentFamily_eq_contour hG hp.1 (by simpa only [mem_ball, dist_zero_right] using hp.2)
  exact (hd.congr_of_eventuallyEq he).differentiableWithinAt

end

end OAI.AlgebraicGeometry.Comparison.Betti.ParametricPositiveLaurent.Dolbeault
