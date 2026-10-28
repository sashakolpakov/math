import OAI.Analysis.PDE.Concentration.Packet.Measure
import OAI.Analysis.PDE.Concentration.SpatialLatticeCell
import OAI.Analysis.PDE.Concentration.CellBoundary

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green

theorem spatialPacketEmbedding_eq_coordinates (d : ℕ) (y : OAI.Analysis.Calculus.Current.SpatialSpace d)
    (q : Option (Fin d) → ℂ) :
    spatialPacketEmbedding d y q = OAI.Analysis.PDE.Green.physicalSpatialEmbedding d (spatialPiCoordinates d y) q := by
  unfold spatialPacketEmbedding
  congr 1
  ext i
  exact (spatialPiCoordinates_apply y i).symm

theorem spatialFiberEquiv_physicalEmbedding {d : ℕ}
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ))
    (x : Fin (d + 1) → ℝ) (q : Option (Fin d) → ℂ) :
    spatialFiberEquiv L (OAI.Analysis.PDE.Green.physicalSpatialEmbedding d x q) = OAI.Analysis.PDE.Green.physicalSpatialEmbedding d (L x) q := by
  ext ⟨i, α⟩
  fin_cases α <;>
    simp [spatialFiberEquiv_apply, spatialFiberChange, OAI.Analysis.PDE.Green.physicalSpatialEmbedding_eq,
      OAI.Analysis.PDE.Green.spatialRealComplexEmbedding_apply]

theorem spatialPacketEmbedding_lattice {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (y : OAI.Analysis.Calculus.Current.SpatialSpace d) (q : Option (Fin d) → ℂ) :
    spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) (spatialPacketEmbedding d y q) =
      spatialPacketEmbedding d ((100 : ℝ) • R y) q := by
  rw [spatialPacketEmbedding_eq_coordinates, spatialFiberEquiv_physicalEmbedding,
    sideHundredLattice_apply, spatialFramePi_apply, spatialPacketEmbedding_eq_coordinates, map_smul]

theorem spatialPiCoordinates_mem_unitCube {d : ℕ} (y : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    spatialPiCoordinates d y ∈ Icc (0 : Fin (d + 1) → ℝ) 1 ↔
      y.ofLp ∈ Icc (0 : Option (Fin d) → ℝ) 1 := by
  constructor
  · rintro ⟨hl, hu⟩
    constructor
    · intro i
      simpa only [Pi.zero_apply, spatialPiCoordinates_apply, Equiv.apply_symm_apply] using
        hl ((finSuccEquiv d).symm i)
    · intro i
      simpa only [Pi.one_apply, spatialPiCoordinates_apply, Equiv.apply_symm_apply] using
        hu ((finSuccEquiv d).symm i)
  · rintro ⟨hl, hu⟩
    constructor
    · intro i
      simpa only [Pi.zero_apply, spatialPiCoordinates_apply] using hl (finSuccEquiv d i)
    · intro i
      simpa only [Pi.one_apply, spatialPiCoordinates_apply] using hu (finSuccEquiv d i)

/-- Exact equality of the closed physical Green cell and the product cell
in packet coordinates. The only later change is its null boundary. -/
theorem physicalPacketSplit_latticeCell {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (a : ℝ) (τ : ℂ) :
    spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) '' OAI.Analysis.PDE.Green.physicalSpatialFiber d a τ =
      (physicalPacketSplit d) ⁻¹' (closedPhysicalSpatialCell R ×ˢ
        {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0}) := by
  let L := sideHundredLattice (spatialFramePi R)
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    let x := (physicalPacketSplit d v).1
    let q := (physicalPacketSplit d v).2
    have hv' : v = spatialPacketEmbedding d x q := by
      rw [← physicalPacketSplit_symm]
      exact ((physicalPacketSplit d).symm_apply_apply v).symm
    change physicalPacketSplit d (spatialFiberEquiv L v) ∈
      closedPhysicalSpatialCell R ×ˢ {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0}
    rw [hv', spatialPacketEmbedding_lattice, physicalPacketSplit_apply,
      spatialPacketEmbedding_real, spatialPacketEmbedding_projection]
    have hc : spatialPiCoordinates d x ∈ Icc 0 1 ∧ OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0 := by
      rw [hv', spatialPacketEmbedding_eq_coordinates] at hv
      change OAI.Analysis.PDE.Green.physicalSpatialEquiv d ((OAI.Analysis.PDE.Green.physicalSpatialEquiv d).symm _) ∈
        Icc (0 : Fin (d + 1) → ℝ) 1 ×ˢ {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0} at hv
      simpa only [MeasurableEquiv.apply_symm_apply, Set.mem_prod, Set.mem_ofPred_eq] using hv
    exact ⟨⟨x.ofLp, (spatialPiCoordinates_mem_unitCube x).mp hc.1, rfl⟩, hc.2⟩
  · intro hw
    change physicalPacketSplit d w ∈
      closedPhysicalSpatialCell R ×ˢ {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0} at hw
    rw [physicalPacketSplit_apply] at hw
    obtain ⟨⟨x, hx, hxeq⟩, hq⟩ := hw
    let v := spatialPacketEmbedding d (spatialFromCoordinates x) (OAI.Analysis.PDE.Green.physicalSpatialProjection d w)
    refine ⟨v, ?_, ?_⟩
    · change OAI.Analysis.PDE.Green.physicalSpatialEquiv d v ∈ Icc 0 1 ×ˢ _
      rw [show v = OAI.Analysis.PDE.Green.physicalSpatialEmbedding d
        (spatialPiCoordinates d (spatialFromCoordinates x)) (OAI.Analysis.PDE.Green.physicalSpatialProjection d w)
        from spatialPacketEmbedding_eq_coordinates _ _ _]
      change OAI.Analysis.PDE.Green.physicalSpatialEquiv d ((OAI.Analysis.PDE.Green.physicalSpatialEquiv d).symm _) ∈ _
      rw [MeasurableEquiv.apply_symm_apply]
      exact ⟨(spatialPiCoordinates_mem_unitCube _).mpr hx, hq⟩
    · change spatialFiberEquiv L (spatialPacketEmbedding d (spatialFromCoordinates x)
        (OAI.Analysis.PDE.Green.physicalSpatialProjection d w)) = w
      rw [spatialPacketEmbedding_lattice, show (100 : ℝ) • R (spatialFromCoordinates x) =
        physicalSpatialRealVector d w from hxeq, ← physicalPacketSplit_symm,
        ← physicalPacketSplit_apply, MeasurableEquiv.symm_apply_apply]

/-- The Green-cell integral is exactly the iterated packet integral, with no
Jacobian factor: the packet spatial variable already carries Euclidean volume. -/
theorem integral_physicalLatticeFiber {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (a : ℝ) (τ : ℂ)
    (hT : MeasurableSet {q : Option (Fin d) → ℂ | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0})
    {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 → ℝ}
    (hf : IntegrableOn f (spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) ''
      OAI.Analysis.PDE.Green.physicalSpatialFiber d a τ)) :
    (∫ y in spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) ''
      OAI.Analysis.PDE.Green.physicalSpatialFiber d a τ, f y) =
      ∫ q in {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0},
        ∫ x in physicalSpatialCell R, f (spatialPacketEmbedding d x q) := by
  rw [physicalPacketSplit_latticeCell] at hf ⊢
  rw [physicalPacketSplit_setIntegral (isCompact_closedPhysicalSpatialCell R).measurableSet hT hf]
  apply integral_congr_ae
  filter_upwards [] with q
  exact integral_closedPhysicalSpatialCell R _

end OAI.Analysis.PDE.Concentration
