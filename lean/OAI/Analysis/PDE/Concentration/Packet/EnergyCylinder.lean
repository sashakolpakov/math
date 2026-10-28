import OAI.Analysis.PDE.Concentration.Packet.Hessian
import OAI.Analysis.PDE.Concentration.Packet.Propagation
import OAI.Analysis.PDE.Concentration.Packet.Cylinder

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped ContDiff Topology Matrix.Norms.Elementwise ComplexOrder MatrixOrder

def packetEnergy {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ) (κ cR cI : ι → ℝ)
    (v : ι → Fin d → ℝ) (lam : ℝ) (u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ) :=
  OAI.Analysis.PDE.Green.setFiberCombinedEnergy OAI.Analysis.Calculus.Quaternion.threeSlots lam (physicalLatticeEnergyCell R a)
    (physicalLatticeCurrent R h a κ cR cI v) (fun x => lam * physicalBackground d x) u

theorem packet_energy_nonneg_of_equation {n m : ℕ} {ι : Type*} [Fintype ι]
    (c : (Fin (n + 3) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
    {lam : ℝ} (hlam : 0 < lam) {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 3) 3 → ℝ}
    (hu : ContDiff ℝ 3 u)
    (hup : ∀ (j : Fin (n + 2)) x, u (x + physicalCellPeriod c R j) = u x)
    (hu0 : ∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain (n + 1) a, u x ≤ 0)
    (huz : ∀ x, (a < ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection (n + 1) x).1‖ ∧
      ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection (n + 1) x).1‖ < 4) → OAI.Analysis.PDE.Green.physicalFullDefining (n + 1) a x = 0 → u x = 0)
    (hDpos : ∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain (n + 1) a,
      (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun y => lam * physicalBackground (n + 1) y + u y) x).submatrix Fin.succ Fin.succ)).PosDef)
    (hequation : ∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain (n + 1) a,
      OAI.LinearAlgebra.Moore.mooreDet (n + 2) ((OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun y => lam * physicalBackground (n + 1) y + u y) x).submatrix Fin.succ Fin.succ) =
          lam * (physicalLatticeCurrent R h a κ cR cI v x 0 0).re)
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (hz : z ∈ physicalEnergyAnnulus a) :
    0 ≤ packetEnergy R h a κ cR cI v lam u z := by
  have hd (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3)
      (hy : y ∈ (spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) ''
        OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z))) :
      OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain (n + 1) a := by
    refine ⟨?_, ?_⟩
    · simpa only [OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber] using And.intro hz.1 hz.2
    · apply physicalLatticeEnergyCell_fiber_defining_neg R a z
      rwa [physicalLatticeEnergyCell_fiber]
  apply (actual_packet_energy_comparison R h a hh ha κ cR cI v lam hlam z hz.1.le hz.2.le hu
    (physicalCellPeriod_to_fiberPeriod c R hup z) ?_
    (fun y hy => hu0 _ (hd y hy)) ?_ ?_).1
  · intro y hy
    apply huz
    · simpa only [OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber] using And.intro hz.1 hz.2
    · simpa only [OAI.Analysis.PDE.Green.physicalFullDefining, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber, spatialDefiningFunction,
        Function.comp_apply] using hy
  · intro y hy
    rw [packetPotential_spatial_hessian lam (hu.of_le (by norm_num)) z y
      (physicalNullHeight_ne_zero_on_domain ha (hd y hy))]
    exact (hDpos _ (hd y hy)).posSemidef
  · intro y hy
    rw [packetPotential_spatial_hessian lam (hu.of_le (by norm_num)) z y
      (physicalNullHeight_ne_zero_on_domain ha (hd y hy))]
    exact hequation _ (hd y hy)

def packetPropagationError {d m k : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (b : (Fin (d + 1) × Fin 3) ≃ Fin (k + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (ε G : ℝ) : ℝ :=
  |(physicalCellLatticeMap c R).toLinearEquiv.toLinearMap.det| *
    ((d + 2 : ℕ) * ε * G * OAI.Analysis.PDE.Green.physicalCutoffConstant b)

theorem packetPropagationError_nonneg {d m k : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (b : (Fin (d + 1) × Fin 3) ≃ Fin (k + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) {ε G : ℝ} (hε : 0 ≤ ε) (hG : 0 ≤ G) :
    0 ≤ packetPropagationError c b R ε G := by
  unfold packetPropagationError
  exact mul_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hε) hG)
    (OAI.Analysis.PDE.Green.physicalCutoffConstant_nonneg b))

/-- The actual packet-energy concentration theorem on the large rotated
torus. Its only analytic inputs are a smooth periodic admissible solution of
the physical equation and quantitative boundary flux/gradient bounds. -/
theorem exists_actual_packet_energy_cylinder_constant : ∃ C : ℝ, 0 < C ∧
    ∀ (n m k : ℕ) (ι : Type) [Fintype ι]
      (c : (Fin (n + 3) × Fin 3) ≃ Fin (m + 1))
      (b : (Fin (n + 2) × Fin 3) ≃ Fin (k + 1))
      (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)) (h a : ℝ),
    0 < h → 0 < a → 4 * a ≤ 1 →
    ∀ (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ),
    (∀ i j, ∃ l : ℤ, inner ℝ (packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n + 1) j) 1)) = (l : ℝ) * (2 * Real.pi) / 100) →
    ∀ (lam : ℝ), 0 < lam → ∀ u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 3) 3 → ℝ, ContDiff ℝ ∞ u →
    (∀ (j : Fin (n + 2)) x, u (x + physicalCellPeriod c R j) = u x) →
    (∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain (n + 1) a, u x ≤ 0) →
    (∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain (n + 1) a,
      (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun y => lam * physicalBackground (n + 1) y + u y) x).submatrix Fin.succ Fin.succ)).PosDef) →
    (∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain (n + 1) a,
      OAI.LinearAlgebra.Moore.mooreDet (n + 2) ((OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun y => lam * physicalBackground (n + 1) y + u y) x).submatrix Fin.succ Fin.succ) =
          lam * (physicalLatticeCurrent R h a κ cR cI v x 0 0).re) →
    ∀ ε G : ℝ, 0 ≤ ε → 0 ≤ G →
    (∀ x, (a < ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection (n + 1) x).1‖ ∧
        ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection (n + 1) x).1‖ < 4) → OAI.Analysis.PDE.Green.physicalFullDefining (n + 1) a x = 0 →
      u x = 0 ∧
        ‖star (OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots (OAI.Analysis.PDE.Green.physicalFullDefining (n + 1) a) x) ᵥ*
          physicalLatticeCurrent R h a κ cR cI v x‖ ≤ ε ∧
        ‖OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots u x‖ ≤ G) → ∀ θ : ℝ,
    (∫ t in (1 : ℝ)..2, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      packetEnergy R h a κ cR cI v lam u (cylinderEnergyEquiv (cylinderPoint t (2 * a) φ))) ≤
      C * (1 + |Real.log (2 * a)|) ^ 3 *
        (packetEnergy R h a κ cR cI v lam u (cylinderEnergyEquiv (cylinderPoint 0 (4 * a) θ)) +
          4 * packetPropagationError c b R ε G) := by
  obtain ⟨C, hC, hc⟩ := exists_packetEnergy_cylinder_constant
  refine ⟨C, hC, ?_⟩
  intro n m k ι inst c b R h a hh ha ha4 κ cR cI v hfreq lam hlam u hu hup hu0 hD hPDE
    ε G hε hG hboundary θ
  apply hc (n + 1) ι R h a hh ha ha4 κ cR cI v OAI.Analysis.Calculus.Quaternion.threeSlots lam u hu
    (packetPropagationError c b R ε G) (packetPropagationError_nonneg c b R hε hG) ?_ ?_ θ
  · intro η hη hηs hs hp
    have hw := packet_combined_energy_weak_bound c b R h a hh ha κ cR cI v hfreq hlam
      (hu.of_le (by simp)) hup hD hPDE hε hG hboundary (hη.of_le (by simp)) hηs hp hs
    simpa only [packetPropagationError, mul_assoc] using hw
  · intro z hz
    exact packet_energy_nonneg_of_equation c R h a hh ha κ cR cI v hlam
      (hu.of_le (by simp)) hup hu0 (fun x ht hr => (hboundary x ht hr).1) hD hPDE z hz

end OAI.Analysis.PDE.Concentration
