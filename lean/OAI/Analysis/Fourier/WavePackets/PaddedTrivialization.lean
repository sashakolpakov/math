import OAI.Analysis.Fourier.WavePackets.PhysicalTrivialization
import OAI.Analysis.Fourier.WavePackets.PaddingLattice
import OAI.Analysis.PDE.Green.ActualSmooth

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped ContDiff

def paddedPhysicalSplit (d : ℕ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 ≃L[ℝ]
    ((Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ)) × (Option (Fin d) → ℂ) :=
  paddedLatticeSplit (OAI.Analysis.PDE.Concentration.physicalSpatialSplit d)

def paddedPhysicalDefining (d : ℕ) (a : ℝ) (τ : ℂ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4) : ℝ :=
  OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ (paddedPhysicalSplit d x).2

theorem paddedPhysicalDefining_eq (d : ℕ) (a : ℝ) (τ : ℂ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4) :
    paddedPhysicalDefining d a τ x = OAI.Analysis.PDE.Concentration.spatialDefiningFunction d a τ (dropFourth (d + 1) x) := by
  simp only [paddedPhysicalDefining, paddedPhysicalSplit, paddedLatticeSplit_apply,
    OAI.Analysis.PDE.Concentration.physicalSpatialSplit_snd, OAI.Analysis.PDE.Concentration.spatialDefiningFunction, Function.comp_apply]

/-- The exact moving-fiber chart in the four-slot coordinates used by
Dirichlet continuation. It fixes both the physical and dummy periodic factors. -/
def paddedPhysicalTransport (d : ℕ) (a : ℝ) (τ₀ τ : ℂ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4) :
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 :=
  (paddedPhysicalSplit d).symm ((paddedPhysicalSplit d x).1,
    physicalFiberTransport a τ₀ τ (paddedPhysicalSplit d x).2)

theorem paddedPhysicalTransport_split (d : ℕ) (a : ℝ) (τ₀ τ : ℂ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4) :
    paddedPhysicalSplit d (paddedPhysicalTransport d a τ₀ τ x) =
      ((paddedPhysicalSplit d x).1, physicalFiberTransport a τ₀ τ (paddedPhysicalSplit d x).2) :=
  (paddedPhysicalSplit d).apply_symm_apply _

theorem paddedPhysicalTransport_defining (d : ℕ) (a : ℝ) (τ₀ τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4}
    (hx : paddedPhysicalDefining d a τ₀ x ≤ 0) :
    paddedPhysicalDefining d a τ (paddedPhysicalTransport d a τ₀ τ x) =
      paddedPhysicalDefining d a τ₀ x := by
  simpa only [paddedPhysicalDefining, paddedPhysicalTransport_split] using
    physicalFiberTransport_defining a τ₀ τ ha ht hx

theorem paddedPhysicalTransport_inverse (d : ℕ) (a : ℝ) (τ₀ τ : ℂ)
    (ha : 0 < a) (ht₀ : a ≤ ‖τ₀‖) (ht : a ≤ ‖τ‖) {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4}
    (hx : paddedPhysicalDefining d a τ₀ x ≤ 0) :
    paddedPhysicalTransport d a τ τ₀ (paddedPhysicalTransport d a τ₀ τ x) = x := by
  apply (paddedPhysicalSplit d).injective
  rw [paddedPhysicalTransport_split, paddedPhysicalTransport_split,
    physicalFiberTransport_inverse a τ₀ τ ha ht₀ ht hx]

theorem paddedPhysicalTransport_self (d : ℕ) (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4}
    (hx : paddedPhysicalDefining d a τ x ≤ 0) : paddedPhysicalTransport d a τ τ x = x := by
  apply (paddedPhysicalSplit d).injective
  rw [paddedPhysicalTransport_split, physicalFiberTransport_self a τ ha ht hx]

theorem contDiffAt_paddedPhysicalTransport_joint (d : ℕ) (a : ℝ) (τ₀ τ : ℂ)
    (ha : 0 < a) (ht₀ : a ≤ ‖τ₀‖) {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4}
    (hx : paddedPhysicalDefining d a τ₀ x ≤ 0) :
    ContDiffAt ℝ ∞ (fun p : ℂ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 =>
      paddedPhysicalTransport d a τ₀ p.1 p.2) (τ,x) := by
  have hp : ContDiff ℝ ∞ (fun p : ℂ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 =>
      (p.1, (paddedPhysicalSplit d p.2).2)) := by fun_prop
  have hq := (contDiffAt_physicalFiberTransport_joint a τ₀ τ ha ht₀ hx).comp (τ,x) hp.contDiffAt
  have hr : ContDiff ℝ ∞ (fun p : ℂ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 =>
      (paddedPhysicalSplit d p.2).1) := by fun_prop
  exact (paddedPhysicalSplit d).symm.contDiff.contDiffAt.comp (τ,x) (hr.contDiffAt.prodMk hq)

theorem contDiffAt_paddedPhysicalTransport_reverse_joint (d : ℕ) (a : ℝ) (τ₀ τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4}
    (hx : paddedPhysicalDefining d a τ x ≤ 0) :
    ContDiffAt ℝ ∞ (fun p : ℂ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 =>
      paddedPhysicalTransport d a p.1 τ₀ p.2) (τ,x) := by
  have hp : ContDiff ℝ ∞ (fun p : ℂ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 =>
      (p.1, (paddedPhysicalSplit d p.2).2)) := by fun_prop
  have hq := (contDiffAt_physicalFiberTransport_reverse_joint a τ₀ τ ha ht hx).comp (τ,x) hp.contDiffAt
  have hr : ContDiff ℝ ∞ (fun p : ℂ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 =>
      (paddedPhysicalSplit d p.2).1) := by fun_prop
  exact (paddedPhysicalSplit d).symm.contDiff.contDiffAt.comp (τ,x) (hr.contDiffAt.prodMk hq)

end OAI.Analysis.Fourier.WavePackets
