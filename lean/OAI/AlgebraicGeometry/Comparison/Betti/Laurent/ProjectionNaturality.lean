import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.LaurentSplitting
import Mathlib.Analysis.Complex.Liouville

/-! # Projection Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Laurent.ProjectionNaturality.Dolbeault

noncomputable section

section

/-! The normalized entire and inverse-coordinate parts are unique.
Liouville's theorem applies to the actual limit at infinity. -/

open _root_.Complex Set Filter
open scoped _root_.Topology

theorem normalizedLaurent_pair_zero {a b : ℂ → ℂ} (ha : Differentiable ℂ a)
    (hb : Differentiable ℂ b) (hb0 : b 0 = 0)
    (h : ∀ z ≠ 0, a z + b z⁻¹ = 0) : (∀ z, a z = 0) ∧ ∀ u, b u = 0 := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  have he : (fun z : ℂ => -b z⁻¹) =ᶠ[cocompact ℂ] a := by
    have hn : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 := isCompact_singleton.compl_mem_cocompact
    filter_upwards [hn] with z hz
    have hz' := h z hz
    linear_combination -hz'
  have ht : Tendsto a (cocompact ℂ) (𝓝 0) := by
    have hc : Tendsto b (𝓝 0) (𝓝 (b 0)) := hb.continuous.continuousAt
    simpa only [hb0, neg_zero] using
      ((hc.comp hi).neg.congr' he)
  have ha0 : ∀ z, a z = 0 := fun z => ha.apply_eq_of_tendsto_cocompact z ht
  refine ⟨ha0, ?_⟩
  intro u
  by_cases hu : u = 0
  · simpa only [hu] using hb0
  · have hu' := h u⁻¹ (inv_ne_zero hu)
    simpa only [ha0, zero_add, inv_inv] using hu'

theorem normalizedLaurent_pair_unique {a b c d : ℂ → ℂ}
    (ha : Differentiable ℂ a) (hb : Differentiable ℂ b)
    (hc : Differentiable ℂ c) (hd : Differentiable ℂ d)
    (hb0 : b 0 = 0) (hd0 : d 0 = 0)
    (h : ∀ z ≠ 0, a z + b z⁻¹ = c z + d z⁻¹) : a = c ∧ b = d := by
  have hz : ∀ z ≠ 0, (a z - c z) + (b z⁻¹ - d z⁻¹) = 0 := by
    intro z hz
    linear_combination h z hz
  obtain ⟨h₁, h₂⟩ := normalizedLaurent_pair_zero (ha.sub hc) (hb.sub hd)
    (by simp only [Pi.sub_apply, hb0, hd0, sub_self]) hz
  exact ⟨funext (fun z => sub_eq_zero.mp (h₁ z)), funext (fun z => sub_eq_zero.mp (h₂ z))⟩

end

/-! The actual normalized Laurent projections preserve linear operations
and coordinate rescaling, by the proved uniqueness of the decomposition. -/

open _root_.Complex Set

theorem laurentProjection_eq_of_decomposition {f a b : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))
    (ha : Differentiable ℂ a) (hb : Differentiable ℂ b) (hb0 : b 0 = 0)
    (h : ∀ z ≠ 0, f z = a z + b z⁻¹) :
    AnnularCauchyFormula.Dolbeault.positiveLaurentPart f = a ∧ Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart f = b := by
  apply normalizedLaurent_pair_unique (AnnularCauchyFormula.Dolbeault.positiveLaurentPart_entire hf) (Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart_entire hf)
    ha hb (Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart_zero f) hb0
  intro z hz
  exact (Holomorphic.LaurentSplitting.Dolbeault.holomorphicLaurentSplitting_identity f hz).trans (h z hz)

theorem laurentProjection_add {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))
    (hg : DifferentiableOn ℂ g (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ)) :
    AnnularCauchyFormula.Dolbeault.positiveLaurentPart (f + g) = AnnularCauchyFormula.Dolbeault.positiveLaurentPart f + AnnularCauchyFormula.Dolbeault.positiveLaurentPart g ∧
      Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart (f + g) = Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart f + Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart g := by
  apply laurentProjection_eq_of_decomposition (hf.add hg)
    ((AnnularCauchyFormula.Dolbeault.positiveLaurentPart_entire hf).add (AnnularCauchyFormula.Dolbeault.positiveLaurentPart_entire hg))
    ((Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart_entire hf).add (Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart_entire hg))
    (by simp only [Pi.add_apply, Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart_zero, add_zero])
  intro z hz
  have hfz := Holomorphic.LaurentSplitting.Dolbeault.holomorphicLaurentSplitting_identity f hz
  have hgz := Holomorphic.LaurentSplitting.Dolbeault.holomorphicLaurentSplitting_identity g hz
  simp only [Pi.add_apply]
  linear_combination -hfz - hgz

theorem laurentProjection_const_mul {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ)) (c : ℂ) :
    AnnularCauchyFormula.Dolbeault.positiveLaurentPart (fun z => c * f z) = (fun z => c * AnnularCauchyFormula.Dolbeault.positiveLaurentPart f z) ∧
      Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart (fun z => c * f z) = (fun z => c * Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart f z) := by
  apply laurentProjection_eq_of_decomposition (hf.const_mul c)
    ((AnnularCauchyFormula.Dolbeault.positiveLaurentPart_entire hf).const_mul c) ((Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart_entire hf).const_mul c)
    (by rw [Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart_zero, mul_zero])
  intro z hz
  rw [← mul_add, Holomorphic.LaurentSplitting.Dolbeault.holomorphicLaurentSplitting_identity f hz]

theorem laurentProjection_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    AnnularCauchyFormula.Dolbeault.positiveLaurentPart f = f ∧ Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart f = 0 := by
  apply laurentProjection_eq_of_decomposition hf.differentiableOn hf (differentiable_const 0) rfl
  intro z _
  exact (add_zero (f z)).symm

theorem laurentProjection_congr {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))
    (hg : DifferentiableOn ℂ g (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))
    (h : ∀ z ≠ 0, f z = g z) :
    AnnularCauchyFormula.Dolbeault.positiveLaurentPart f = AnnularCauchyFormula.Dolbeault.positiveLaurentPart g ∧ Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart f = Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart g := by
  apply laurentProjection_eq_of_decomposition hf (AnnularCauchyFormula.Dolbeault.positiveLaurentPart_entire hg)
    (Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart_entire hg) (Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart_zero g)
  intro z hz
  exact (h z hz).trans (Holomorphic.LaurentSplitting.Dolbeault.holomorphicLaurentSplitting_identity g hz).symm

theorem laurentProjection_inverse_entire {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    AnnularCauchyFormula.Dolbeault.positiveLaurentPart (fun z => g z⁻¹) = (fun _ => g 0) ∧
      Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart (fun z => g z⁻¹) = (fun u => g u - g 0) := by
  have hginv : DifferentiableOn ℂ (fun z => g z⁻¹) (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ) := by
    intro z hz
    exact ((hg z⁻¹).comp z (differentiableAt_inv hz)).differentiableWithinAt
  apply laurentProjection_eq_of_decomposition hginv (differentiable_const (g 0)) (hg.sub_const (g 0))
    (sub_self _)
  intro z _
  ring

theorem laurentProjection_rescale {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ)) {c : ℂ} (hc : c ≠ 0) :
    AnnularCauchyFormula.Dolbeault.positiveLaurentPart (fun z => f (c * z)) = (fun z => AnnularCauchyFormula.Dolbeault.positiveLaurentPart f (c * z)) ∧
      Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart (fun z => f (c * z)) = (fun u => Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart f (c⁻¹ * u)) := by
  have hmul : Differentiable ℂ (fun z : ℂ => c * z) := differentiable_id.const_mul c
  have hinv : Differentiable ℂ (fun u : ℂ => c⁻¹ * u) := differentiable_id.const_mul c⁻¹
  have hfc : DifferentiableOn ℂ (fun z => f (c * z)) (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ) :=
    hf.comp hmul.differentiableOn (fun _ hz => mul_ne_zero hc hz)
  apply laurentProjection_eq_of_decomposition hfc
    ((AnnularCauchyFormula.Dolbeault.positiveLaurentPart_entire hf).comp hmul) ((Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart_entire hf).comp hinv)
    (by rw [Function.comp_apply, mul_zero, Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart_zero])
  intro z hz
  simpa only [mul_inv, Function.comp_apply] using (Holomorphic.LaurentSplitting.Dolbeault.holomorphicLaurentSplitting_identity f (mul_ne_zero hc hz)).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Laurent.ProjectionNaturality.Dolbeault
