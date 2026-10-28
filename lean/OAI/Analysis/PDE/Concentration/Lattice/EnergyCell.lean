import OAI.Analysis.PDE.Concentration.Physical.LatticeChart
import OAI.Analysis.PDE.Green.Physical.TimeSupport

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green

theorem fiberEmbedding_timeSpace {n s : ℕ} (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s) :
    OAI.Analysis.PDE.Green.fiberEmbedding n s (OAI.Analysis.PDE.Green.timeProjection n s x) (OAI.Analysis.PDE.Green.timeSpaceEquiv n s x).2 = x := by
  rw [← OAI.Analysis.PDE.Green.timeSpaceEquiv_fst, ← OAI.Analysis.PDE.Green.timeSpaceEquiv_symm_apply]
  exact (OAI.Analysis.PDE.Green.timeSpaceEquiv n s).symm_apply_apply x

theorem fiber_image_congr {n s : ℕ}
    (L : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s ≃L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s)
    (hL : ∀ x, OAI.Analysis.PDE.Green.timeProjection n s (L x) = OAI.Analysis.PDE.Green.timeProjection n s x)
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s) {S T : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s)}
    (hST : (OAI.Analysis.PDE.Green.fiberEmbedding n s z) ⁻¹' S = (OAI.Analysis.PDE.Green.fiberEmbedding n s z) ⁻¹' T) :
    (OAI.Analysis.PDE.Green.fiberEmbedding n s z) ⁻¹' (L '' S) = (OAI.Analysis.PDE.Green.fiberEmbedding n s z) ⁻¹' (L '' T) := by
  have hm (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s) (hx : OAI.Analysis.PDE.Green.timeProjection n s x = z) :
      x ∈ S ↔ x ∈ T := by
    have hh := Set.ext_iff.mp hST (OAI.Analysis.PDE.Green.timeSpaceEquiv n s x).2
    simpa only [Set.mem_preimage, ← hx, fiberEmbedding_timeSpace] using hh
  ext y
  have ht : OAI.Analysis.PDE.Green.timeProjection n s (L.symm (OAI.Analysis.PDE.Green.fiberEmbedding n s z y)) = z := by
    rw [← hL, ContinuousLinearEquiv.apply_symm_apply, OAI.Analysis.PDE.Green.timeProjection_fiberEmbedding]
  have him (V : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s)) :
      OAI.Analysis.PDE.Green.fiberEmbedding n s z y ∈ L '' V ↔ L.symm (OAI.Analysis.PDE.Green.fiberEmbedding n s z y) ∈ V := by
    constructor
    · rintro ⟨x, hx, heq⟩
      rw [← heq, ContinuousLinearEquiv.symm_apply_apply]
      exact hx
    · intro hx
      exact ⟨_, hx, L.apply_symm_apply _⟩
  exact (him S).trans ((hm _ ht).trans (him T).symm)

def physicalLatticeEnergyCell {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (a : ℝ) :
    Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :=
  physicalLatticeEquiv (sideHundredLattice (spatialFramePi R)) '' OAI.Analysis.PDE.Green.physicalEnergyCell d a

theorem physicalLattice_sublevel_image {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (lo hi : Fin (m + 1) → ℝ)
    (r : (ℂ × (Option (Fin d) → ℂ)) → ℝ) :
    euclideanLatticeCell c (physicalCellLatticeMap c R) lo hi ∩
        {x | r (OAI.Analysis.PDE.Green.fullPhysicalProjection d x) < 0} =
      physicalLatticeEquiv (sideHundredLattice (spatialFramePi R)) ''
        ((OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc lo hi) ∩ {x | r (OAI.Analysis.PDE.Green.fullPhysicalProjection d x) < 0}) := by
  ext x
  constructor
  · rintro ⟨⟨y, hy, heq⟩, hr⟩
    refine ⟨(OAI.Analysis.PDE.Green.euclideanCoordinates c).symm y, ⟨?_, ?_⟩, ?_⟩
    · simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hy
    · have hx : physicalLatticeEquiv (sideHundredLattice (spatialFramePi R))
          ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm y) = x := by
        rw [← physicalCellLatticeMap_apply, heq, ContinuousLinearEquiv.symm_apply_apply]
      change r (OAI.Analysis.PDE.Green.fullPhysicalProjection d x) < 0 at hr
      rw [← hx, fullPhysicalProjection_latticeEquiv] at hr
      exact hr
    · rw [← physicalCellLatticeMap_apply, heq, ContinuousLinearEquiv.symm_apply_apply]
  · rintro ⟨y, ⟨hy, hr⟩, rfl⟩
    refine ⟨⟨OAI.Analysis.PDE.Green.euclideanCoordinates c y, hy, ?_⟩, ?_⟩
    · apply (OAI.Analysis.PDE.Green.euclideanCoordinates c).symm.injective
      rw [physicalCellLatticeMap_apply, ContinuousLinearEquiv.symm_apply_apply,
        ContinuousLinearEquiv.symm_apply_apply]
    · simpa only [Set.mem_ofPred_eq, fullPhysicalProjection_latticeEquiv] using hr

theorem physicalLatticeTimeBox_weak_energy_eq {d m k : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (b : (Fin (d + 1) × Fin 3) ≃ Fin (k + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (H a : ℝ) (ha : 0 < a)
    (η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ)
    (ht : ∀ z ∈ tsupport η, a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ∧ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ≤ 4)
    (hz : ∀ z ∈ tsupport η, ∀ j : Fin 3, -H ≤ z (0, j) ∧ z (0, j) ≤ H)
    (r : (ℂ × (Option (Fin d) → ℂ)) → ℝ)
    (hneg : ∀ z ∈ tsupport η, ∀ q, r (OAI.Analysis.PDE.Green.energyComplexTime z, q) < 0 ↔
      OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (OAI.Analysis.PDE.Green.energyComplexTime z) q < 0)
    (e : Fin 3 → Quaternion ℝ) (lam : ℝ)
    (A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → Matrix (Fin (d + 2)) (Fin (d + 2)) (Quaternion ℝ))
    (B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ) :
    (∫ z, Laplacian.laplacian η z * OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam
      (euclideanLatticeCell c (physicalCellLatticeMap c R)
        (OAI.Analysis.PDE.Green.physicalTimeBoxLower c H) (OAI.Analysis.PDE.Green.physicalTimeBoxUpper c H) ∩
        {x | r (OAI.Analysis.PDE.Green.fullPhysicalProjection d x) < 0}) A B u z) =
      ∫ z, Laplacian.laplacian η z *
        OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (physicalLatticeEnergyCell R a) A B u z := by
  rw [physicalLattice_sublevel_image]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  by_cases hΔ : Laplacian.laplacian η z = 0
  · simp only [hΔ, zero_mul]
  · have hzs := OAI.Analysis.PDE.Green.laplacian_nonzero_mem_tsupport hΔ
    have hs := OAI.Analysis.PDE.Green.physicalTimeBox_sublevel_fiber_eq c b H a ha z
      (ht z hzs).1 (ht z hzs).2 (hz z hzs) r (hneg z hzs)
    have heq := fiber_image_congr (physicalLatticeEquiv (sideHundredLattice (spatialFramePi R)))
      (physicalLatticeEquiv_timeProjection _) z (hs.trans (OAI.Analysis.PDE.Green.physicalEnergyCell_fiber d a z).symm)
    simp only [OAI.Analysis.PDE.Green.setFiberCombinedEnergy, physicalLatticeEnergyCell, heq]

end OAI.Analysis.PDE.Concentration
