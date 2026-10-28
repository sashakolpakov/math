import OAI.Analysis.PDE.Green.WeakLaplacian
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Measure-preserving separation of the extended-time block from spatial fibers. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore

def timeSpaceIndexEquiv (n s : ℕ) :
    (Fin 1 × Fin s) ⊕ (Fin n × Fin s) ≃ Fin (n + 1) × Fin s where
  toFun := Sum.elim (fun p => (0, p.2)) (fun p => (p.1.succ, p.2))
  invFun p := Fin.cases (Sum.inl (0, p.2)) (fun i => Sum.inr (i, p.2)) p.1
  left_inv p := by
    rcases p with ⟨i, α⟩ | ⟨i, α⟩
    · have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl
    · rfl
  right_inv p := by
    rcases p with ⟨i, α⟩
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl

def timeSpaceEquiv (n s : ℕ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s ≃ᵐ
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s × OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s :=
  (MeasurableEquiv.toLp 2 ((Fin (n + 1) × Fin s) → ℝ)).symm |>.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (timeSpaceIndexEquiv n s).symm) |>.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ)) |>.trans
    ((MeasurableEquiv.toLp 2 ((Fin 1 × Fin s) → ℝ)).prodCongr
      (MeasurableEquiv.toLp 2 ((Fin n × Fin s) → ℝ)))

theorem measurePreserving_timeSpaceEquiv (n s : ℕ) :
    MeasurePreserving (timeSpaceEquiv n s) := by
  exact (((PiLp.volume_preserving_ofLp (Fin (n + 1) × Fin s)).trans
    (volume_measurePreserving_piCongrLeft (fun _ => ℝ) (timeSpaceIndexEquiv n s).symm)).trans
    (volume_measurePreserving_sumPiEquivProdPi (fun _ => ℝ))).trans
    ((PiLp.volume_preserving_toLp (Fin 1 × Fin s)).prod
      (PiLp.volume_preserving_toLp (Fin n × Fin s)))

theorem timeSpaceEquiv_fst (n s : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s) :
    (timeSpaceEquiv n s x).1 = timeProjection n s x := by
  ext ⟨i, α⟩
  have hi : i = 0 := Fin.eq_zero i
  subst i
  change MeasurableEquiv.piCongrLeft (fun _ => ℝ) (timeSpaceIndexEquiv n s).symm
    (WithLp.ofLp x) ((timeSpaceIndexEquiv n s).symm (0, α)) = x (0, α)
  exact MeasurableEquiv.piCongrLeft_apply_apply _ _ _

theorem timeSpaceEquiv_snd_apply (n s : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s)
    (i : Fin n) (α : Fin s) :
    (timeSpaceEquiv n s x).2 (i, α) = x (i.succ, α) := by
  change MeasurableEquiv.piCongrLeft (fun _ => ℝ) (timeSpaceIndexEquiv n s).symm
    (WithLp.ofLp x) ((timeSpaceIndexEquiv n s).symm (i.succ, α)) = x (i.succ, α)
  exact MeasurableEquiv.piCongrLeft_apply_apply _ _ _

def spatialInjectionLinear (n s : ℕ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s →ₗ[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s where
  toFun x := WithLp.toLp 2 (fun p => Fin.cases 0 (fun i => x (i, p.2)) p.1)
  map_add' x y := by
    ext ⟨i, α⟩
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  map_smul' c x := by
    ext ⟨i, α⟩
    refine Fin.cases ?_ (fun i => ?_) i <;> simp

def spatialInjection (n s : ℕ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s :=
  (spatialInjectionLinear n s).toContinuousLinearMap

def timeInjection (n s : ℕ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s :=
  WithLp.toLp 2 (fun p => Fin.cases (z (0, p.2)) (fun _ => 0) p.1)

def fiberEmbedding (n s : ℕ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s := timeInjection n s z + spatialInjection n s y

theorem timeSpaceEquiv_symm_apply (n s : ℕ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s)
    (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    (timeSpaceEquiv n s).symm (z, y) = fiberEmbedding n s z y := by
  apply (timeSpaceEquiv n s).injective
  rw [MeasurableEquiv.apply_symm_apply]
  apply Prod.ext
  · rw [timeSpaceEquiv_fst]
    ext ⟨i, α⟩
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp [timeProjection, timeProjectionLinear, fiberEmbedding, timeInjection,
      spatialInjection, spatialInjectionLinear]
  · ext ⟨i, α⟩
    rw [timeSpaceEquiv_snd_apply]
    simp [fiberEmbedding, timeInjection,
      spatialInjection, spatialInjectionLinear]

theorem timeProjection_fiberEmbedding (n s : ℕ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s)
    (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) : timeProjection n s (fiberEmbedding n s z y) = z := by
  rw [← timeSpaceEquiv_fst, ← timeSpaceEquiv_symm_apply, MeasurableEquiv.apply_symm_apply]

theorem continuous_fiberEmbedding (n s : ℕ) :
    Continuous (fun p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s × OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s => fiberEmbedding n s p.1 p.2) := by
  have ht : Continuous (timeInjection n s) := by
    unfold timeInjection
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) × Fin s => ℝ)).comp
    apply continuous_pi
    intro p
    refine Fin.cases ?_ (fun i => ?_) p.1
    · exact PiLp.continuous_apply 2 (fun _ : Fin 1 × Fin s => ℝ) (0, p.2)
    · exact continuous_const
  exact (ht.comp continuous_fst).add ((spatialInjection n s).continuous.comp continuous_snd)

/-- Fubini for the actual extended-time and spatial coordinates. -/
theorem integral_fiberEmbedding {n s : ℕ} {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ}
    (hf : Integrable f) :
    (∫ x, f x) = ∫ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s, ∫ y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s,
      f (fiberEmbedding n s z y) := by
  have hmp := (measurePreserving_timeSpaceEquiv n s).symm
  have hi : Integrable (fun p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s × OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s =>
      f ((timeSpaceEquiv n s).symm p)) := hmp.integrable_comp_of_integrable hf
  calc
    _ = ∫ p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s × OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s, f ((timeSpaceEquiv n s).symm p) :=
      (hmp.integral_comp (timeSpaceEquiv n s).symm.measurableEmbedding f).symm
    _ = ∫ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s, ∫ y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s,
        f ((timeSpaceEquiv n s).symm (z, y)) := by
      rw [Measure.volume_eq_prod]
      exact integral_prod _ hi
    _ = _ := by simp only [timeSpaceEquiv_symm_apply]

end OAI.Analysis.PDE.Green
