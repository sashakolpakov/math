import OAI.Analysis.PDE.Concentration.Lattice.EnergyCell

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green

def spatialFiberChange {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (y : Fin n × Fin 3 → ℝ) (p : Fin n × Fin 3) : ℝ :=
  if p.2 = 0 then L (fun i => y (i, 0)) p.1 else y p

def spatialFiberLinearEquiv {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
    (Fin n × Fin 3 → ℝ) ≃ₗ[ℝ] (Fin n × Fin 3 → ℝ) where
  toFun := spatialFiberChange L
  invFun := spatialFiberChange L.symm
  left_inv y := by
    funext ⟨i, α⟩
    by_cases hα : α = 0 <;> simp [spatialFiberChange, hα]
  right_inv y := by
    funext ⟨i, α⟩
    by_cases hα : α = 0 <;> simp [spatialFiberChange, hα]
  map_add' y z := by
    funext ⟨i, α⟩
    by_cases hα : α = 0
    · subst α
      exact congrFun (L.map_add (fun k => y (k, 0)) (fun k => z (k, 0))) i
    · simp [spatialFiberChange, hα]
  map_smul' r y := by
    funext ⟨i, α⟩
    by_cases hα : α = 0
    · subst α
      exact congrFun (L.map_smul r (fun k => y (k, 0))) i
    · simp [spatialFiberChange, hα]

def spatialFiberEquiv {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 3 ≃L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n × Fin 3 => ℝ)).trans
    ((spatialFiberLinearEquiv L).toContinuousLinearEquiv.trans
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n × Fin 3 => ℝ)).symm)

theorem spatialFiberEquiv_apply {n : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 3) (p : Fin n × Fin 3) :
    spatialFiberEquiv L y p = spatialFiberChange L (fun q => y q) p := rfl

theorem physicalLatticeEquiv_fiberEmbedding {d : ℕ}
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ))
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) :
    physicalLatticeEquiv L (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y) =
      OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z (spatialFiberEquiv L y) := by
  ext ⟨i, α⟩
  rw [physicalLatticeEquiv_apply]
  refine Fin.cases ?_ (fun i => ?_) i
  · by_cases hα : α = 0 <;> simp [spatialRealChange, hα, OAI.Analysis.PDE.Green.fiberEmbedding_apply_zero]
  · by_cases hα : α = 0 <;>
      simp [spatialRealChange, spatialFiberEquiv_apply, spatialFiberChange, hα,
        OAI.Analysis.PDE.Green.fiberEmbedding_apply_succ]

theorem physicalLatticeEnergyCell_fiber {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (a : ℝ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) :
    (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z) ⁻¹' physicalLatticeEnergyCell R a =
      spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) ''
        OAI.Analysis.PDE.Green.physicalSpatialFiber d a (OAI.Analysis.PDE.Green.energyComplexTime z) := by
  let L := sideHundredLattice (spatialFramePi R)
  have hs : ∀ y, OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y ∈ OAI.Analysis.PDE.Green.physicalEnergyCell d a ↔
      y ∈ OAI.Analysis.PDE.Green.physicalSpatialFiber d a (OAI.Analysis.PDE.Green.energyComplexTime z) := by
    intro y
    exact Set.ext_iff.mp (OAI.Analysis.PDE.Green.physicalEnergyCell_fiber d a z) y
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    have ht : OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 x = z := by
      rw [← physicalLatticeEquiv_timeProjection L, hxy, OAI.Analysis.PDE.Green.timeProjection_fiberEmbedding]
    have hx' : OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z (OAI.Analysis.PDE.Green.timeSpaceEquiv (d + 1) 3 x).2 = x := by
      rw [← ht, fiberEmbedding_timeSpace]
    have hmem : OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z (OAI.Analysis.PDE.Green.timeSpaceEquiv (d + 1) 3 x).2 ∈
        OAI.Analysis.PDE.Green.physicalEnergyCell d a := by
      rw [hx']
      exact hx
    refine ⟨(OAI.Analysis.PDE.Green.timeSpaceEquiv (d + 1) 3 x).2, (hs _).mp hmem, ?_⟩
    have he : OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z (spatialFiberEquiv L (OAI.Analysis.PDE.Green.timeSpaceEquiv (d + 1) 3 x).2) =
        OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y := by
      rw [← physicalLatticeEquiv_fiberEmbedding, hx']
      exact hxy
    have hp := congrArg (OAI.Analysis.PDE.Green.timeSpaceEquiv (d + 1) 3) he
    simpa only [← OAI.Analysis.PDE.Green.timeSpaceEquiv_symm_apply, MeasurableEquiv.apply_symm_apply, Prod.mk.injEq,
      true_and] using hp
  · rintro ⟨y, hy, rfl⟩
    refine ⟨OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y, (hs y).mpr hy, ?_⟩
    exact physicalLatticeEquiv_fiberEmbedding L z y

end OAI.Analysis.PDE.Concentration
