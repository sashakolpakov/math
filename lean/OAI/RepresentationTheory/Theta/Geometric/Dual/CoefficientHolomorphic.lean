import OAI.RepresentationTheory.Theta.Geometric.ScalarFirstJet
import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.Gluing

/-! # Coefficient Holomorphic -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.CoefficientHolomorphic

noncomputable section

/-! Holomorphy and gluing of both coefficients of actual dual-number
comparison functions. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

def DualCoefficientDifferentiableAt (c : V → DualNumber ℂ) (z : V) : Prop :=
  DifferentiableAt ℂ (fun w => (c w).fst) z ∧
    DifferentiableAt ℂ (fun w => (c w).snd) z

theorem dualCoefficientDifferentiableAt_mul (c d : V → DualNumber ℂ) (z : V)
    (hc : DualCoefficientDifferentiableAt c z) (hd : DualCoefficientDifferentiableAt d z) :
    DualCoefficientDifferentiableAt (fun w => c w * d w) z := by
  constructor
  · simpa only [TrivSqZeroExt.fst_mul] using hc.1.fun_mul hd.1
  · simpa only [DualNumber.snd_mul] using
      (hc.1.fun_mul hd.2).fun_add (hc.2.fun_mul hd.1)

theorem dualCoefficientDifferentiableAt_inv (c : V → DualNumber ℂ) (z : V)
    (hc : DualCoefficientDifferentiableAt c z) (hz : (c z).fst ≠ 0) :
    DualCoefficientDifferentiableAt (fun w => (c w)⁻¹) z := by
  constructor
  · simpa only [TrivSqZeroExt.fst_inv] using hc.1.fun_inv hz
  · change DifferentiableAt ℂ (fun w => -((c w).fst⁻¹ * (c w).snd * (c w).fst⁻¹)) z
    exact (((hc.1.fun_inv hz).fun_mul hc.2).fun_mul (hc.1.fun_inv hz)).neg

theorem exists_dualCoefficientDifferentiable_gluing {ι : Type*}
    (U : ι → Set V) (C : ι → V → DualNumber ℂ)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hdiff : ∀ i x, x ∈ U i → DualCoefficientDifferentiableAt (C i) x)
    (hcompat : ∀ i j x, x ∈ U i → x ∈ U j → C i x = C j x) :
    ∃ c : V → DualNumber ℂ, (∀ x, DualCoefficientDifferentiableAt c x) ∧
      ∀ i x, x ∈ U i → c x = C i x := by
  obtain ⟨f, hf, hfm⟩ := Holomorphic.Gluing.exists_differentiable_gluing U (fun i x => (C i x).fst)
    hopen hcover (fun i x hx => (hdiff i x hx).1)
    (fun i j x hi hj => congrArg TrivSqZeroExt.fst (hcompat i j x hi hj))
  obtain ⟨g, hg, hgm⟩ := Holomorphic.Gluing.exists_differentiable_gluing U (fun i x => (C i x).snd)
    hopen hcover (fun i x hx => (hdiff i x hx).2)
    (fun i j x hi hj => congrArg TrivSqZeroExt.snd (hcompat i j x hi hj))
  refine ⟨fun x => (f x, g x), fun x => ⟨hf x, hg x⟩, ?_⟩
  intro i x hx
  exact TrivSqZeroExt.ext (hfm i x hx) (hgm i x hx)

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.CoefficientHolomorphic
