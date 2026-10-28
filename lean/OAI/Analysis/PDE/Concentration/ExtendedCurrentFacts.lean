import OAI.Analysis.PDE.Concentration.ExtendedEnergy
import OAI.Analysis.PDE.Concentration.Physical.CellPeriod
import OAI.Analysis.PDE.Concentration.Physical.RankOne
import OAI.Analysis.PDE.Green.Physical.Propagation

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped ContDiff Topology Matrix.Norms.Elementwise ComplexOrder MatrixOrder

theorem extendedPhysicalLatticeCurrent_isHermitian {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    (extendedPhysicalLatticeCurrent R h a ha κ cR cI v x).IsHermitian := by
  by_cases hx : physicalNullHeight d x = 0
  · have hz := (awayZeroCutoff_eq_zero_near a ha).eq_of_nhds
    simp only [extendedPhysicalLatticeCurrent, awayZeroExtension, hx, hz, Pi.zero_apply,
      zero_smul]
    exact isHermitian_zero
  · have hA := physicalLatticeCurrent_isHermitian R h a hh κ cR cI v x hx
    change (awayZeroCutoff a ha (physicalNullHeight d x) •
      physicalLatticeCurrent R h a κ cR cI v x)ᴴ = _
    apply funext
    intro i
    apply funext
    intro j
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Quaternion.star_smul]
    exact congrArg (fun q : Quaternion ℝ => awayZeroCutoff a ha (physicalNullHeight d x) • q)
      (congrFun (congrFun hA i) j)

theorem extendedPhysicalLatticeCurrent_cellPeriod {d m : ℕ} {ι : Type*} [Fintype ι]
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ) (ha : 0 < a)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (j : Fin (d + 1))
    (hfreq : ∀ k, ∃ l : ℤ, inner ℝ (packetSpatialFrequency (κ k) (v k))
      (R (EuclideanSpace.single (finSuccEquiv d j) 1)) = (l : ℝ) * (2 * Real.pi) / 100)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    extendedPhysicalLatticeCurrent R h a ha κ cR cI v (x + physicalCellPeriod c R j) =
      extendedPhysicalLatticeCurrent R h a ha κ cR cI v x := by
  rw [physicalCellPeriod_eq]
  have hp := extendedPhysicalLatticeCurrent_periodic R h a ha κ cR cI v
    (finSuccEquiv d j) hfreq
    (x - physicalSpatialTranslate ((100 : ℝ) • R (EuclideanSpace.single (finSuccEquiv d j) 1)))
  exact hp.symm.trans (congrArg (extendedPhysicalLatticeCurrent R h a ha κ cR cI v)
    (sub_add_cancel x _))

theorem extendedPhysicalBackground_cellPeriod {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (a : ℝ) (ha : 0 < a)
    (j : Fin (d + 1)) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    extendedPhysicalBackground d a ha (x + physicalCellPeriod c R j) =
      extendedPhysicalBackground d a ha x := by
  rw [physicalCellPeriod_eq]
  have hp := extendedPhysicalBackground_periodic d a ha
    ((100 : ℝ) • R (EuclideanSpace.single (finSuccEquiv d j) 1))
    (x - physicalSpatialTranslate ((100 : ℝ) • R (EuclideanSpace.single (finSuccEquiv d j) 1)))
  exact hp.symm.trans (congrArg (extendedPhysicalBackground d a ha) (sub_add_cancel x _))

theorem physicalNullHeight_ne_zero_on_domain {d : ℕ} {a : ℝ} (ha : 0 < a)
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3} (hx : x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain d a) :
    physicalNullHeight d x ≠ 0 :=
  norm_pos_iff.mp (ha.trans_le (physicalNullHeight_on_closed_fiber d a ha x hx.1.1.le hx.2.le))

theorem extendedPhysicalBackground_scaled_hessian {d : ℕ} (a : ℝ) (ha : 0 < a)
    (lam : ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
    (ht : a ≤ ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖) (hr : OAI.Analysis.PDE.Green.physicalFullDefining d a x ≤ 0) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun y => lam * extendedPhysicalBackground d a ha y) x =
      lam • OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (physicalBackground d) x := by
  have hg := awayZeroExtension_eq_near a ha (contDiff_physicalNullHeight d).continuous
    (physicalBackground d) (physicalNullHeight_on_closed_fiber d a ha x ht hr)
  rw [show (fun y => lam * extendedPhysicalBackground d a ha y) =
    (fun y => lam • extendedPhysicalBackground d a ha y) from rfl,
    OAI.Analysis.PDE.Dirichlet.quaternionHessian_smul OAI.Analysis.Calculus.Quaternion.threeSlots ((contDiff_extendedPhysicalBackground d a ha).of_le (by simp))]
  change extendedPhysicalBackground d a ha =ᶠ[𝓝 x] physicalBackground d at hg
  rw [OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.threeSlots hg]

theorem physicalBackground_hessian_posSemidef {d : ℕ} (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
    (hx : physicalNullHeight d x ≠ 0) :
    (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (physicalBackground d) x)).PosSemidef := by
  rw [physicalBackground_hessian_rank_one d x hx, OAI.LinearAlgebra.Moore.complexify_real_smul]
  exact (OAI.LinearAlgebra.Moore.complexify_outer_posSemidef _).smul (by norm_num)

end OAI.Analysis.PDE.Concentration
