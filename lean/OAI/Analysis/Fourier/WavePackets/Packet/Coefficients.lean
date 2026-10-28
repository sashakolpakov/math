import OAI.Analysis.Fourier.WavePackets.PulledCoefficients
import OAI.Analysis.Fourier.WavePackets.Packet.FixedData

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Concentration OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Topology ContDiff Matrix.Norms.Elementwise

local instance {ι : Type*} [Fintype ι] : NormedAddCommGroup (Matrix ι ι (Quaternion ℝ)) :=
  inferInstanceAs (NormedAddCommGroup (ι → ι → Quaternion ℝ))
local instance {ι : Type*} [Fintype ι] : NormedSpace ℝ (Matrix ι ι (Quaternion ℝ)) :=
  inferInstanceAs (NormedSpace ℝ (ι → ι → Quaternion ℝ))

def packetPaddedEmbedding (n : ℕ) (p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4) :
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 3) 3 := OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 p.1 (dropFourth (n + 2) p.2)

theorem contDiff_packetPaddedEmbedding (n : ℕ) : ContDiff ℝ ∞ (packetPaddedEmbedding n) :=
  (OAI.Analysis.PDE.Green.contDiff_fiberEmbedding (n + 2) 3 ∞).comp
    (contDiff_fst.prodMk ((dropFourth (n + 2)).contDiff.comp contDiff_snd))

def packetPaddedBackground (n : ℕ) (a : ℝ) (ha : 0 < a) (lam : ℝ)
    (p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4) : ℝ :=
  lam * OAI.Analysis.PDE.Concentration.extendedPhysicalBackground (n + 1) a ha (packetPaddedEmbedding n p)

def packetPaddedSource {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (ha : 0 < a) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ) (lam : ℝ)
    (p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4) : ℝ :=
  lam * (OAI.Analysis.PDE.Concentration.extendedPhysicalLatticeCurrent R h a ha κ cR cI v (packetPaddedEmbedding n p) 0 0).re

theorem contDiff_packetPaddedBackground (n : ℕ) (a : ℝ) (ha : 0 < a) (lam : ℝ) :
    ContDiff ℝ ∞ (packetPaddedBackground n a ha lam) :=
  contDiff_const.mul ((OAI.Analysis.PDE.Concentration.contDiff_extendedPhysicalBackground (n + 1) a ha).comp
    (contDiff_packetPaddedEmbedding n))

theorem contDiff_packetPaddedSource {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ) (lam : ℝ) :
    ContDiff ℝ ∞ (packetPaddedSource R h a ha κ cR cI v lam) := by
  have hA : ContDiff ℝ ∞ (fun p =>
      (OAI.Analysis.PDE.Concentration.extendedPhysicalLatticeCurrent R h a ha κ cR cI v (packetPaddedEmbedding n p) :
        Fin (n + 3) → Fin (n + 3) → Quaternion ℝ)) :=
    (OAI.Analysis.PDE.Concentration.contDiff_extendedPhysicalLatticeCurrent R h a hh ha κ cR cI v).comp
      (contDiff_packetPaddedEmbedding n)
  exact contDiff_const.mul ((OAI.Analysis.PDE.Green.contDiff_quaternion_real ∞).comp
    ((contDiff_apply_apply ℝ (Quaternion ℝ) 0 0).comp hA))

theorem packetPaddedBackground_periodic {n : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (a : ℝ) (ha : 0 < a) (lam : ℝ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit (n + 1)) (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R))
      (fun x => packetPaddedBackground n a ha lam (z,x)) := by
  apply latticePeriodic_dropFourth (OAI.Analysis.PDE.Concentration.physicalSpatialSplit (n + 1)) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)
    (f := fun y => lam * OAI.Analysis.PDE.Concentration.extendedPhysicalBackground (n + 1) a ha (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y))
  apply OAI.Analysis.PDE.Concentration.latticePeriodic_fiber_of_cell_period (OAI.Analysis.PDE.Concentration.packetFullCoordinates n) R
    (u := fun x => lam * OAI.Analysis.PDE.Concentration.extendedPhysicalBackground (n + 1) a ha x) (z := z)
  intro j x
  rw [OAI.Analysis.PDE.Concentration.extendedPhysicalBackground_cellPeriod (OAI.Analysis.PDE.Concentration.packetFullCoordinates n) R a ha j x]

theorem packetPaddedSource_periodic {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (ha : 0 < a) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n + 1) j) 1)) = (l : ℝ) * (2 * Real.pi) / 100)
    (lam : ℝ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit (n + 1)) (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R))
      (fun x => packetPaddedSource R h a ha κ cR cI v lam (z,x)) := by
  apply latticePeriodic_dropFourth (OAI.Analysis.PDE.Concentration.physicalSpatialSplit (n + 1)) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)
    (f := fun y => lam * (OAI.Analysis.PDE.Concentration.extendedPhysicalLatticeCurrent R h a ha κ cR cI v
      (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) 0 0).re)
  apply OAI.Analysis.PDE.Concentration.latticePeriodic_fiber_of_cell_period (OAI.Analysis.PDE.Concentration.packetFullCoordinates n) R
    (u := fun x => lam * (OAI.Analysis.PDE.Concentration.extendedPhysicalLatticeCurrent R h a ha κ cR cI v x 0 0).re) (z := z)
  intro j x
  rw [OAI.Analysis.PDE.Concentration.extendedPhysicalLatticeCurrent_cellPeriod (OAI.Analysis.PDE.Concentration.packetFullCoordinates n) R h a ha κ cR cI v j
    (fun i => hfreq i j) x]

def packetPaddedBackgroundHessian (n : ℕ) (a : ℝ) (ha : 0 < a) (lam : ℝ)
    (p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4) :
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (fun x => packetPaddedBackground n a ha lam (p.1,x))) p.2

theorem contDiff_packetPaddedBackgroundHessian (n : ℕ) (a : ℝ) (ha : 0 < a) (lam : ℝ) :
    ContDiff ℝ ∞ (packetPaddedBackgroundHessian n a ha lam) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact contDiffAt_spatial_fderiv (contDiffAt_spatial_fderiv
    (contDiff_packetPaddedBackground n a ha lam).contDiffAt)

theorem packetPaddedBackgroundHessian_periodic {n : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (a : ℝ) (ha : 0 < a) (lam : ℝ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit (n + 1)) (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R))
      (fun x => packetPaddedBackgroundHessian n a ha lam (z,x)) :=
  (packetPaddedBackground_periodic R a ha lam z).fderiv.fderiv

end OAI.Analysis.Fourier.WavePackets
