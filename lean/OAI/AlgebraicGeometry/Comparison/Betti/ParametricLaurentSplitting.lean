import OAI.AlgebraicGeometry.Comparison.Betti.ParametricPositiveLaurent
import OAI.AlgebraicGeometry.Comparison.Betti.InvertedCauchyCircle
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.LaurentSplitting

/-! # Parametric Laurent Splitting -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ParametricLaurentSplitting.Dolbeault

noncomputable section

/-! Normalized Laurent splitting preserves joint holomorphy on every
open finite-dimensional complex parameter domain. -/

open _root_.Complex Set _root_.Metric Filter
open scoped _root_.Topology

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]

def negativeLaurentFamily (G : P × ℂ → ℂ) (q : P × ℂ) : ℂ :=
  Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart (fun w => G (q.1, w)) q.2

theorem negativeLaurentFamily_holomorphic {G : P × ℂ → ℂ} {S : Set P} (hS : IsOpen S)
    (hG : DifferentiableOn ℂ G (S ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))) :
    DifferentiableOn ℂ (negativeLaurentFamily G) (S ×ˢ univ) := by
  intro q hq
  by_cases hz : q.2 = 0
  · have hmem : q ∈ S ×ˢ ball (0 : ℂ) 1 := ⟨hq.1, by simp [hz]⟩
    have hd := (InvertedCauchyCircle.Dolbeault.invertedUnitCauchyFamily_holomorphic hS hG).differentiableAt
      ((hS.prod isOpen_ball).mem_nhds hmem)
    apply (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [(hS.prod isOpen_ball).mem_nhds hmem] with p hp
    exact Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart_eq_inverted (ParametricPositiveLaurent.Dolbeault.puncturedFamily_slice_holomorphic hG hp.1)
      (by simpa only [mem_ball, dist_zero_right] using hp.2)
  · let J : P × ℂ → P × ℂ := fun p => (p.1, p.2⁻¹)
    have hJ : DifferentiableAt ℂ J q :=
      differentiableAt_fst.prodMk (differentiableAt_snd.fun_inv hz)
    have hg := hG.differentiableAt ((hS.prod PuncturedCauchy.Dolbeault.puncturedComplexOpen.isOpen).mem_nhds
      (show J q ∈ S ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ) from ⟨hq.1, inv_ne_zero hz⟩))
    have ha := (ParametricPositiveLaurent.Dolbeault.positiveLaurentFamily_holomorphic hS hG).differentiableAt
      ((hS.prod isOpen_univ).mem_nhds (show J q ∈ S ×ˢ univ from ⟨hq.1, mem_univ _⟩))
    have hd : DifferentiableAt ℂ (fun p => G (J p) - ParametricPositiveLaurent.Dolbeault.positiveLaurentFamily G (J p)) q :=
      (hg.comp q hJ).sub (ha.comp q hJ)
    apply (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [(isOpen_ne.preimage continuous_snd).mem_nhds hz] with p hp
    simp only [negativeLaurentFamily, Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart, ite_eq_right hp, ParametricPositiveLaurent.Dolbeault.positiveLaurentFamily, J]

omit [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P] in
theorem parametricLaurentSplitting_identity (G : P × ℂ → ℂ) (p : P) {z : ℂ} (hz : z ≠ 0) :
    ParametricPositiveLaurent.Dolbeault.positiveLaurentFamily G (p, z) + negativeLaurentFamily G (p, z⁻¹) = G (p, z) :=
  Holomorphic.LaurentSplitting.Dolbeault.holomorphicLaurentSplitting_identity (fun w => G (p, w)) hz

theorem exists_parametricLaurentSplitting {G : P × ℂ → ℂ} {S : Set P} (hS : IsOpen S)
    (hG : DifferentiableOn ℂ G (S ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))) :
    ∃ a b : P × ℂ → ℂ,
      DifferentiableOn ℂ a (S ×ˢ univ) ∧ DifferentiableOn ℂ b (S ×ˢ univ) ∧
      (∀ p, b (p, 0) = 0) ∧ ∀ p z, z ≠ 0 → G (p, z) = a (p, z) + b (p, z⁻¹) :=
  ⟨ParametricPositiveLaurent.Dolbeault.positiveLaurentFamily G, negativeLaurentFamily G, ParametricPositiveLaurent.Dolbeault.positiveLaurentFamily_holomorphic hS hG,
    negativeLaurentFamily_holomorphic hS hG, fun _ => Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart_zero _,
    fun p _ hz => (parametricLaurentSplitting_identity G p hz).symm⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.ParametricLaurentSplitting.Dolbeault
