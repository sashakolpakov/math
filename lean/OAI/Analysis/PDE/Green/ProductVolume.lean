import OAI.Analysis.PDE.Green.FiberCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! Volume-preserving real/complex separation of the three spatial slots. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set _root_.MeasureTheory
open scoped ContDiff

theorem volume_preserving_uncurry (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℝ).symm := by
  let e := (MeasurableEquiv.curry ι κ ℝ).symm
  refine ⟨e.measurable, ?_⟩
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply e.measurable (MeasurableSet.univ_pi hs)]
  have he : e ⁻¹' Set.pi univ s = Set.pi univ (fun i => Set.pi univ (fun j => s (i, j))) := by
    ext x
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left]
    exact ⟨fun h i j => h (i, j), fun h p => h p.1 p.2⟩
  rw [he, volume_pi_pi]
  simp only [volume_pi_pi, Fintype.prod_prod_type]

theorem volume_preserving_curry (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℝ) :=
  (volume_preserving_uncurry ι κ).symm

def complexRealCoordinates (ι : Type*) : (ι → ℂ) ≃ᵐ (ι × Fin 2 → ℝ) :=
  (MeasurableEquiv.piCongrRight (fun _ : ι => Complex.measurableEquivPi)).trans
    (MeasurableEquiv.curry ι (Fin 2) ℝ).symm

theorem measurePreserving_complexRealCoordinates (ι : Type*) [Fintype ι] :
    MeasurePreserving (complexRealCoordinates ι) := by
  have h : MeasurePreserving
      (MeasurableEquiv.piCongrRight (fun _ : ι => Complex.measurableEquivPi)) :=
    volume_preserving_pi (fun _ => Complex.volume_preserving_equiv_pi)
  exact h.trans (volume_preserving_uncurry ι (Fin 2))

def spatialRealComplexIndex (ι : Type*) : (ι ⊕ (ι × Fin 2)) ≃ (ι × Fin 3) where
  toFun := Sum.elim (fun i => (i, 0)) (fun p => (p.1, p.2.succ))
  invFun p := Fin.cases (Sum.inl p.1) (fun j => Sum.inr (p.1, j)) p.2
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with ⟨i, j⟩; refine Fin.cases ?_ (fun j => ?_) j <;> rfl

def spatialRealComplexEquiv (ι : Type*) :
    EuclideanSpace ℝ (ι × Fin 3) ≃ᵐ ((ι → ℝ) × (ι → ℂ)) :=
  (MeasurableEquiv.toLp 2 ((ι × Fin 3) → ℝ)).symm |>.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (spatialRealComplexIndex ι).symm) |>.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ)) |>.trans
    ((MeasurableEquiv.refl (ι → ℝ)).prodCongr (complexRealCoordinates ι).symm)

theorem measurePreserving_spatialRealComplexEquiv (ι : Type*) [Fintype ι] :
    MeasurePreserving (spatialRealComplexEquiv ι) := by
  exact (((PiLp.volume_preserving_ofLp (ι × Fin 3)).trans
    (volume_measurePreserving_piCongrLeft (fun _ => ℝ) (spatialRealComplexIndex ι).symm)).trans
    (volume_measurePreserving_sumPiEquivProdPi (fun _ => ℝ))).trans
    ((MeasurePreserving.id volume).prod (measurePreserving_complexRealCoordinates ι).symm)

def spatialRealComplexEmbedding (ι : Type*) (x : ι → ℝ) (q : ι → ℂ) :
    EuclideanSpace ℝ (ι × Fin 3) := (spatialRealComplexEquiv ι).symm (x, q)

theorem spatialRealComplexEmbedding_apply (ι : Type*) (x : ι → ℝ) (q : ι → ℂ)
    (i : ι) (j : Fin 3) :
    spatialRealComplexEmbedding ι x q (i, j) = ![x i, (q i).re, (q i).im] j := by
  fin_cases j <;> rfl

def spatialRealComplexEmbeddingLinear (ι : Type*) [Fintype ι] :
    ((ι → ℝ) × (ι → ℂ)) →ₗ[ℝ] EuclideanSpace ℝ (ι × Fin 3) where
  toFun p := spatialRealComplexEmbedding ι p.1 p.2
  map_add' p q := by
    ext ⟨i, j⟩
    simp only [PiLp.add_apply, spatialRealComplexEmbedding_apply]
    fin_cases j <;> rfl
  map_smul' c p := by
    ext ⟨i, j⟩
    simp only [PiLp.smul_apply, spatialRealComplexEmbedding_apply]
    fin_cases j <;> simp

theorem contDiff_spatialRealComplexEmbedding (ι : Type*) [Fintype ι] (k : ℕ∞ω) :
    ContDiff ℝ k (fun p : (ι → ℝ) × (ι → ℂ) => spatialRealComplexEmbedding ι p.1 p.2) :=
  (spatialRealComplexEmbeddingLinear ι).toContinuousLinearMap.contDiff

theorem integral_realComplex_fibers {ι : Type*} [Fintype ι]
    {K : Set (ι → ℝ)} {D : Set (ι → ℂ)} (hK : MeasurableSet K) (hD : MeasurableSet D)
    {f : EuclideanSpace ℝ (ι × Fin 3) → ℝ}
    (hf : IntegrableOn f ((spatialRealComplexEquiv ι) ⁻¹' (K ×ˢ D))) :
    (∫ y in (spatialRealComplexEquiv ι) ⁻¹' (K ×ˢ D), f y) =
      ∫ x in K, ∫ q in D, f (spatialRealComplexEmbedding ι x q) := by
  classical
  let e := spatialRealComplexEquiv ι
  have hKD := hK.prod hD
  have hS : MeasurableSet (e ⁻¹' (K ×ˢ D)) := hKD.preimage e.measurable
  have hmp := (measurePreserving_spatialRealComplexEquiv ι).symm
  have hi := hmp.integrable_comp_of_integrable ((integrable_indicator_iff hS).2 hf)
  have he : (fun p => ((e ⁻¹' (K ×ˢ D)).indicator f) (e.symm p)) =
      (K ×ˢ D).indicator (fun p => f (e.symm p)) := by
    funext p
    have hp : e.symm p ∈ e ⁻¹' (K ×ˢ D) ↔ p ∈ K ×ˢ D := by
      change e (e.symm p) ∈ K ×ˢ D ↔ p ∈ K ×ˢ D
      rw [e.apply_symm_apply]
    simp only [indicator, hp]
  have hp : IntegrableOn (fun p => f (e.symm p)) (K ×ˢ D) :=
    (integrable_indicator_iff hKD).1 (he ▸ hi)
  rw [← integral_indicator hS]
  calc
    _ = ∫ p, ((e ⁻¹' (K ×ˢ D)).indicator f) (e.symm p) :=
      (hmp.integral_comp e.symm.measurableEmbedding _).symm
    _ = ∫ p in K ×ˢ D, f (e.symm p) := by rw [he, integral_indicator hKD]
    _ = _ := by
      rw [Measure.volume_eq_prod] at hp ⊢
      exact setIntegral_prod _ hp

end OAI.Analysis.PDE.Green
