import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Integrability

/-! # Pairing -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Pairing.CM

noncomputable section

/-! The actual adelic Haar pairing is sesquilinear on the complete
Schwartz tensor span and factors on pure tensors. -/

open scoped Classical
open _root_.MeasureTheory
variable {I : Type*} [Fintype I]
variable (μ : Measure (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) [μ.IsAddHaarMeasure]

theorem integrable_pair (F G : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) :
    Integrable (fun x => F.val x * star (G.val x)) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure μ) := by
  refine Submodule.span_induction₂
    (p := fun f g _ _ => Integrable (fun x => f x * star (g x)) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure μ))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ F.property G.property
  · intro f g hf hg
    obtain ⟨f, φ, rfl⟩ := hf
    obtain ⟨g, η, rfl⟩ := hg
    exact Integrability.CM.Pair.tensor_pair μ f g φ η
  · intro g _
    simpa only [Pi.zero_apply, zero_mul] using! (integrable_zero _ _ _ : Integrable (0 : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) → ℂ) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure μ))
  · intro f _
    simpa only [Pi.zero_apply, star_zero, mul_zero] using! (integrable_zero _ _ _ : Integrable (0 : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) → ℂ) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure μ))
  · intro f g h _ _ _ ihf ihg
    simpa only [Pi.add_apply, add_mul] using! ihf.add ihg
  · intro f g h _ _ _ ihg ihh
    simpa only [Pi.add_apply, star_add, mul_add] using! ihg.add ihh
  · intro c f g _ _ ih
    simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc] using ih.const_mul c
  · intro c f g _ _ ih
    convert ih.const_mul (star c) using 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, star_mul]
    ring

def pairing (F G : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) : ℂ :=
  ∫ x, F.val x * star (G.val x) ∂(RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure μ)

omit [μ.IsAddHaarMeasure] in
theorem zero_left (G : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) : pairing μ 0 G = 0 := by simp [pairing]
omit [μ.IsAddHaarMeasure] in
theorem zero_right (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) : pairing μ F 0 = 0 := by simp [pairing]

theorem add_left (F G H : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) : pairing μ (F + G) H = pairing μ F H + pairing μ G H := by
  simp only [pairing, Submodule.coe_add, Pi.add_apply, add_mul]
  exact integral_add (integrable_pair μ F H) (integrable_pair μ G H)

theorem add_right (F G H : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) : pairing μ F (G + H) = pairing μ F G + pairing μ F H := by
  simp only [pairing, Submodule.coe_add, Pi.add_apply, star_add, mul_add]
  exact integral_add (integrable_pair μ F G) (integrable_pair μ F H)

omit [μ.IsAddHaarMeasure] in
theorem smul_left (c : ℂ) (F G : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) : pairing μ (c • F) G = c * pairing μ F G := by
  simp only [pairing, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

omit [μ.IsAddHaarMeasure] in
theorem smul_right (c : ℂ) (F G : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) : pairing μ F (c • G) = star c * pairing μ F G := by
  change (∫ x, F.val x * star (c * G.val x) ∂(RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure μ)) = _
  have he : (fun x => F.val x * star (c * G.val x)) = fun x => star c * (F.val x * star (G.val x)) := by
    funext x
    rw [star_mul]
    ring
  rw [he, integral_const_mul]
  rfl

theorem tensor_pairing (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) (φ η : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    pairing μ (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor h η) =
      (∫ x, f.val x * star (h.val x)) * (∫ y, φ.val y * star (η.val y) ∂μ) := by
  change (∫ x, (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ).val x * star ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor h η).val x)
    ∂Measure.map RepresentationTheory.Theta.AdelicTopology.PoissonAutomorphyConstruction.adelicProductEquiv (volume.prod μ)) = _
  rw [RepresentationTheory.Theta.AdelicTopology.PoissonAutomorphyConstruction.adelicProductEquiv.measurableEmbedding.integral_map]
  calc
    _ = ∫ x : (I → ℝ) × (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf),
        (f.val x.1 * star (h.val x.1)) * (φ.val x.2 * star (η.val x.2)) ∂volume.prod μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change (f.val x.1 * φ.val x.2) * star (h.val x.1 * η.val x.2) = _
        rw [star_mul]
        ring
    _ = _ := by
      simpa only using! integral_prod_mul (μ := volume) (ν := μ)
        (fun x : I → ℝ => f.val x * star (h.val x))
        (fun y : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => φ.val y * star (η.val y))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Pairing.CM
