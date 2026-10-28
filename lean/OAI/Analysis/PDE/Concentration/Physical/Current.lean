import OAI.Analysis.PDE.Concentration.NullCurrent
import OAI.Analysis.Calculus.Current.SourceProperties

noncomputable section
open scoped ContDiff
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet

local instance {ι : Type*} [Fintype ι] : NormedAddCommGroup (Matrix ι ι (Quaternion ℝ)) :=
  inferInstanceAs (NormedAddCommGroup (ι → ι → Quaternion ℝ))
local instance {ι : Type*} [Fintype ι] : NormedSpace ℝ (Matrix ι ι (Quaternion ℝ)) :=
  inferInstanceAs (NormedSpace ℝ (ι → ι → Quaternion ℝ))

def physicalToNullCurrentPoint (d : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) : OAI.Analysis.Calculus.Current.CurrentSpace d :=
  nullCoordinateProjection d (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift (nullRotation d)) x)

/-- The source's exact regularized packet current in physical coordinates,
including the rotation of both matrix indices. -/
def physicalPacketCurrent {d : ℕ} {ι : Type*} [Fintype ι]
    (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) :
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → Matrix (Fin (d + 2)) (Fin (d + 2)) (Quaternion ℝ) :=
  rotatedCurrent (nullRotation d) (nullIndexedCurrent
    (fun q => OAI.Analysis.Calculus.Current.sourceRegularizedCurrent h a κ cR cI v q.1 q.2))

theorem contDiffAt_physicalPacketCurrent {d : ℕ} {ι : Type*} [Fintype ι]
    (h a : ℝ) (hh : 0 < h) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
    (hx : physicalToNullCurrentPoint d x ∈ OAI.Analysis.Calculus.Current.currentNonzeroDomain d) :
    ContDiffAt ℝ ∞ (physicalPacketCurrent h a κ cR cI v) x := by
  apply contDiffAt_rotatedCurrent
  apply contDiffAt_nullIndexedCurrent
  exact OAI.Analysis.Calculus.Current.sourceRegularizedCurrent_contDiffAt h a hh κ cR cI v _ hx

theorem physicalPacketCurrent_strongDivergence_zero {d : ℕ} {ι : Type*} [Fintype ι]
    (h a : ℝ) (hh : 0 < h) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
    (hx : physicalToNullCurrentPoint d x ∈ OAI.Analysis.Calculus.Current.currentNonzeroDomain d) (b : Fin (d + 2)) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence OAI.Analysis.Calculus.Quaternion.threeSlots
      (fun p => fderiv ℝ (physicalPacketCurrent h a κ cR cI v) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) b = 0 := by
  have hA : ContDiffAt ℝ ∞ (fun q : OAI.Analysis.Calculus.Current.CurrentSpace d =>
      (OAI.Analysis.Calculus.Current.sourceRegularizedCurrent h a κ cR cI v q.1 q.2 : OAI.Analysis.Calculus.Current.Index d → OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ))
      (physicalToNullCurrentPoint d x) :=
    OAI.Analysis.Calculus.Current.sourceRegularizedCurrent_contDiffAt h a hh κ cR cI v _ hx
  apply rotatedCurrent_strongDivergence_zero OAI.Analysis.Calculus.Quaternion.threeSlots (nullRotation_orthogonal d)
    ((contDiffAt_nullIndexedCurrent hA).differentiableAt (by simp))
  intro j
  apply nullIndexedCurrent_strongDivergence_zero OAI.Analysis.Calculus.Quaternion.threeSlots (hA.differentiableAt (by simp))
  intro k
  exact OAI.Analysis.Calculus.Current.sourceRegularizedCurrent_divergence_zero h a hh κ cR cI v _ hx k

end OAI.Analysis.PDE.Concentration
