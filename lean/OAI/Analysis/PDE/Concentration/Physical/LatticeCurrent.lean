import OAI.Analysis.PDE.Concentration.CurrentPeriodicity
import OAI.Analysis.PDE.Concentration.Physical.Flux
import OAI.Analysis.PDE.Concentration.Physical.Time

noncomputable section
open scoped ContDiff
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix ComplexOrder

local instance {ι : Type*} [Fintype ι] : NormedAddCommGroup (Matrix ι ι (Quaternion ℝ)) :=
  inferInstanceAs (NormedAddCommGroup (ι → ι → Quaternion ℝ))
local instance {ι : Type*} [Fintype ι] : NormedSpace ℝ (Matrix ι ι (Quaternion ℝ)) :=
  inferInstanceAs (NormedSpace ℝ (ι → ι → Quaternion ℝ))

def physicalLatticeCurrent {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) :
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → Matrix (Fin (d + 2)) (Fin (d + 2)) (Quaternion ℝ) :=
  rotatedCurrent (nullRotation d) (nullIndexedCurrent
    (fun q => latticeRegularizedCurrent R h a κ cR cI v q.1 q.2))

theorem physicalLatticeCurrent_eq_physicalMatrix {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    physicalLatticeCurrent R h a κ cR cI v x = physicalMatrix
      (latticeRegularizedCurrent R h a κ cR cI v
        (physicalToNullCurrentPoint d x).1 (physicalToNullCurrentPoint d x).2) := rfl

theorem contDiffAt_physicalLatticeCurrent {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h a : ℝ) (hh : 0 < h) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
    (hx : physicalToNullCurrentPoint d x ∈ OAI.Analysis.Calculus.Current.currentNonzeroDomain d) :
    ContDiffAt ℝ ∞ (physicalLatticeCurrent R h a κ cR cI v) x := by
  apply contDiffAt_rotatedCurrent
  apply contDiffAt_nullIndexedCurrent
  exact latticeRegularizedCurrent_contDiffAt R h a hh κ cR cI v _ hx

theorem physicalLatticeCurrent_strongDivergence_zero {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h a : ℝ) (hh : 0 < h) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
    (hx : physicalToNullCurrentPoint d x ∈ OAI.Analysis.Calculus.Current.currentNonzeroDomain d) (b : Fin (d + 2)) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence OAI.Analysis.Calculus.Quaternion.threeSlots
      (fun p => fderiv ℝ (physicalLatticeCurrent R h a κ cR cI v) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) b = 0 := by
  have hA : ContDiffAt ℝ ∞ (fun q : OAI.Analysis.Calculus.Current.CurrentSpace d =>
      (latticeRegularizedCurrent R h a κ cR cI v q.1 q.2 : OAI.Analysis.Calculus.Current.Index d → OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ))
      (physicalToNullCurrentPoint d x) :=
    latticeRegularizedCurrent_contDiffAt R h a hh κ cR cI v _ hx
  apply rotatedCurrent_strongDivergence_zero OAI.Analysis.Calculus.Quaternion.threeSlots (nullRotation_orthogonal d)
    ((contDiffAt_nullIndexedCurrent hA).differentiableAt (by simp))
  intro j
  apply nullIndexedCurrent_strongDivergence_zero OAI.Analysis.Calculus.Quaternion.threeSlots (hA.differentiableAt (by simp))
  intro k
  exact latticeRegularizedCurrent_divergence_zero R h a hh κ cR cI v _ hx k

theorem physicalLatticeCurrent_isHermitian {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h a : ℝ) (hh : 0 < h) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : (physicalToNullCurrentPoint d x).2 none ≠ 0) :
    Matrix.IsHermitian (physicalLatticeCurrent R h a κ cR cI v x) := by
  apply matrixConjugationCLM_isHermitian
  apply nullMatrixReindex_isHermitian
  exact latticeRegularizedCurrent_isHermitian R h a hh κ cR cI v _ _ hx

theorem physicalLatticeCurrent_posSemidef {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h a : ℝ) (hh : 0 < h) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : (physicalToNullCurrentPoint d x).2 none ≠ 0) :
    (OAI.LinearAlgebra.Moore.complexify (physicalLatticeCurrent R h a κ cR cI v x)).PosSemidef := by
  apply matrixConjugationCLM_posSemidef
  apply nullMatrixReindex_posSemidef
  exact latticeRegularizedCurrent_posSemidef R h a hh κ cR cI v _ _ hx

theorem physicalLatticeCurrent_time_entry {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    (physicalLatticeCurrent R h a κ cR cI v x 0 0).re =
      OAI.Analysis.Calculus.Current.timeComponent (latticeRegularizedCurrent R h a κ cR cI v
        (physicalToNullCurrentPoint d x).1 (physicalToNullCurrentPoint d x).2) :=
  nullRotation_time_entry _

theorem physicalLatticeCurrent_time_pos {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h a : ℝ) (hh : 0 < h) (ha : a ≠ 0) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : (physicalToNullCurrentPoint d x).2 none ≠ 0)
    (hr : OAI.Analysis.Calculus.Current.fiberDefining (1 / 10) a (physicalToNullCurrentPoint d x).2 ≤ 0) :
    0 < (physicalLatticeCurrent R h a κ cR cI v x 0 0).re := by
  rw [physicalLatticeCurrent_time_entry]
  exact latticeRegularizedCurrent_time_pos R h a hh ha κ cR cI v _ _ hx hr

theorem physicalBackground_mul_latticeCurrent_zero {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h a : ℝ) (hh : 0 < h) (ha : a ≠ 0) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : (physicalToNullCurrentPoint d x).2 none ≠ 0) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (physicalBackground d) x *
      physicalLatticeCurrent R h a κ cR cI v x = 0 := by
  rw [physicalBackground_hessian d x hx, physicalLatticeCurrent_eq_physicalMatrix]
  apply physicalMatrix_mul_zero
  exact latticeRegularizedCurrent_background_mul R h a hh ha κ cR cI v _ _ hx

end OAI.Analysis.PDE.Concentration
