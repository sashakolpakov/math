import OAI.Analysis.PDE.Concentration.Packet.PeriodBasis
import OAI.Analysis.PDE.Concentration.LocalLatticeExtension

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped ContDiff

def timeSpaceSplit (n s : ℕ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s ≃L[ℝ]
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s × OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s where
    toEquiv := (OAI.Analysis.PDE.Green.timeSpaceEquiv n s).toEquiv
    map_add' := by
      intro x y
      change OAI.Analysis.PDE.Green.timeSpaceEquiv n s (x + y) = OAI.Analysis.PDE.Green.timeSpaceEquiv n s x + OAI.Analysis.PDE.Green.timeSpaceEquiv n s y
      apply Prod.ext
      · simp only [Prod.fst_add, OAI.Analysis.PDE.Green.timeSpaceEquiv_fst, map_add]
      · ext ⟨i, α⟩
        simp only [OAI.Analysis.PDE.Green.timeSpaceEquiv_snd_apply, PiLp.add_apply, Prod.snd_add]
    map_smul' := by
      intro c x
      change OAI.Analysis.PDE.Green.timeSpaceEquiv n s (c • x) = c • OAI.Analysis.PDE.Green.timeSpaceEquiv n s x
      apply Prod.ext
      · simp only [Prod.smul_fst, OAI.Analysis.PDE.Green.timeSpaceEquiv_fst, map_smul]
      · ext ⟨i, α⟩
        simp only [OAI.Analysis.PDE.Green.timeSpaceEquiv_snd_apply, PiLp.smul_apply, Prod.smul_snd]
    continuous_toFun := by
      change Continuous (fun x => OAI.Analysis.PDE.Green.timeSpaceEquiv n s x)
      apply Continuous.prodMk
      · change Continuous (fun x => (OAI.Analysis.PDE.Green.timeSpaceEquiv n s x).1)
        simpa only [OAI.Analysis.PDE.Green.timeSpaceEquiv_fst] using (OAI.Analysis.PDE.Green.timeProjection n s).continuous
      · apply (PiLp.continuous_toLp 2 (fun _ : Fin n × Fin s => ℝ)).comp
        apply continuous_pi
        intro ⟨i, α⟩
        change Continuous (fun x => (OAI.Analysis.PDE.Green.timeSpaceEquiv n s x).2 (i, α))
        simpa only [OAI.Analysis.PDE.Green.timeSpaceEquiv_snd_apply] using
          (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) × Fin s => ℝ) (i.succ, α))
    continuous_invFun := by
      change Continuous (fun p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s × OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s =>
        (OAI.Analysis.PDE.Green.timeSpaceEquiv n s).symm (p.1, p.2))
      simpa only [OAI.Analysis.PDE.Green.timeSpaceEquiv_symm_apply] using OAI.Analysis.PDE.Green.continuous_fiberEmbedding n s

theorem timeSpaceSplit_fst (n s : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s) :
    (timeSpaceSplit n s x).1 = OAI.Analysis.PDE.Green.timeProjection n s x := OAI.Analysis.PDE.Green.timeSpaceEquiv_fst n s x

theorem timeSpaceSplit_symm (n s : ℕ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    (timeSpaceSplit n s).symm (z, y) = OAI.Analysis.PDE.Green.fiberEmbedding n s z y := OAI.Analysis.PDE.Green.timeSpaceEquiv_symm_apply n s z y

/-- Real periodic coordinates are separated from time and complex transverse
coordinates without changing the physical spatial lattice. -/
def fullPhysicalSplit (d : ℕ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 ≃L[ℝ]
    (Fin (d + 1) → ℝ) × (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × (Option (Fin d) → ℂ)) :=
  (timeSpaceSplit (d + 1) 3).trans
    (((ContinuousLinearEquiv.refl ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)).prodCongr (physicalSpatialSplit d)).trans
    ((ContinuousLinearEquiv.prodAssoc ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (Fin (d + 1) → ℝ)
      (Option (Fin d) → ℂ)).symm.trans
    (((ContinuousLinearEquiv.prodComm ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (Fin (d + 1) → ℝ)).prodCongr
      (ContinuousLinearEquiv.refl ℝ (Option (Fin d) → ℂ))).trans
    (ContinuousLinearEquiv.prodAssoc ℝ (Fin (d + 1) → ℝ) (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
      (Option (Fin d) → ℂ)))))

theorem fullPhysicalSplit_snd_fst (d : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    (fullPhysicalSplit d x).2.1 = OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 x := OAI.Analysis.PDE.Green.timeSpaceEquiv_fst _ _ _

theorem fullPhysicalSplit_symm (d : ℕ) (p : Fin (d + 1) → ℝ)
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (q : Option (Fin d) → ℂ) :
    (fullPhysicalSplit d).symm (p, z, q) =
      OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z (OAI.Analysis.PDE.Green.physicalSpatialEmbedding d p q) := OAI.Analysis.PDE.Green.timeSpaceEquiv_symm_apply _ _ _ _

theorem fullPhysicalSplit_fullProjection (d : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    OAI.Analysis.PDE.Green.fullPhysicalProjection d x =
      (OAI.Analysis.PDE.Green.energyComplexTime (fullPhysicalSplit d x).2.1, (fullPhysicalSplit d x).2.2) := by
  obtain ⟨⟨p, z, q⟩, rfl⟩ := (fullPhysicalSplit d).symm.surjective x
  rw [ContinuousLinearEquiv.apply_symm_apply, fullPhysicalSplit_symm,
    OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber, OAI.Analysis.PDE.Green.physicalSpatialProjection_embedding]

theorem fullPhysicalSplit_period {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (j : Fin (d + 1)) :
    (fullPhysicalSplit d).symm (packetSpatialBasis R j, 0) = physicalCellPeriod c R j := by
  rw [show (0 : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × (Option (Fin d) → ℂ)) = (0, 0) from rfl,
    fullPhysicalSplit_symm, ← physicalSpatialSplit_symm, packetSpatialBasis_period]
  rw [spatial_coordinateVector_eq_packetEmbedding, spatialPacketEmbedding_lattice]
  have he := fiberEmbedding_add_packetEmbedding_real (0 : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (0 : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) ((100 : ℝ) • R (EuclideanSpace.single (finSuccEquiv d j) 1))
  have hz : OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 0 0 = 0 := by
    ext ⟨i, α⟩
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp only [OAI.Analysis.PDE.Green.fiberEmbedding_apply_zero, OAI.Analysis.PDE.Green.fiberEmbedding_apply_succ, PiLp.zero_apply]
  simpa only [zero_add, hz, zero_sub, physicalCellPeriod_eq] using he

theorem latticePeriodic_full_of_cell_period {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ}
    (hp : ∀ (j : Fin (d + 1)) x, u (x + physicalCellPeriod c R j) = u x) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic (fullPhysicalSplit d) (packetSpatialBasis R) u := by
  apply latticePeriodic_of_basis_periods
  intro j
  rw [fullPhysicalSplit_period c R j]
  exact hp j

theorem cell_period_of_latticePeriodic_full {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ}
    (hp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic (fullPhysicalSplit d) (packetSpatialBasis R) u)
    (j : Fin (d + 1)) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    u (x + physicalCellPeriod c R j) = u x := by
  let z : Submodule.span ℤ (range (packetSpatialBasis R)) :=
    ⟨packetSpatialBasis R j, Submodule.subset_span (mem_range_self j)⟩
  have he : x + physicalCellPeriod c R j = (fullPhysicalSplit d).symm
      (((fullPhysicalSplit d) x).1 + (z : Fin (d + 1) → ℝ), ((fullPhysicalSplit d) x).2) := by
    rw [← fullPhysicalSplit_period c R j]
    apply (fullPhysicalSplit d).injective
    simp only [map_add, ContinuousLinearEquiv.apply_symm_apply]
    ext <;> simp [z]
  rw [he]
  exact hp x z

end OAI.Analysis.PDE.Concentration
