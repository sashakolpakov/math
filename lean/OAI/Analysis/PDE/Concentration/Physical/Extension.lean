import OAI.Analysis.PDE.Concentration.AwayZeroExtension
import OAI.Analysis.PDE.Concentration.Physical.Geometry
import OAI.Analysis.PDE.Concentration.Packet.Frequency
import OAI.Analysis.Calculus.Current.Physical.Compact

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

local instance physicalExtensionMatrixNormedAddCommGroup {ι : Type*} [Fintype ι] :
    NormedAddCommGroup (Matrix ι ι (Quaternion ℝ)) :=
  inferInstanceAs (NormedAddCommGroup (ι → ι → Quaternion ℝ))
local instance physicalExtensionMatrixNormedSpace {ι : Type*} [Fintype ι] :
    NormedSpace ℝ (Matrix ι ι (Quaternion ℝ)) :=
  inferInstanceAs (NormedSpace ℝ (ι → ι → Quaternion ℝ))

def physicalNullHeight (d : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) : ℂ :=
  (physicalToNullCurrentPoint d x).2 none

theorem contDiff_physicalNullHeight (d : ℕ) : ContDiff ℝ ∞ (physicalNullHeight d) := by
  unfold physicalNullHeight physicalToNullCurrentPoint
  fun_prop

theorem physicalNullHeight_spatialTranslate (d : ℕ) (y : OAI.Analysis.Calculus.Current.SpatialSpace d)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    physicalNullHeight d (x + physicalSpatialTranslate y) = physicalNullHeight d x := by
  simp only [physicalNullHeight, physicalToNullCurrentPoint_add,
    physicalToNullCurrentPoint_spatialTranslate, Prod.snd_add, add_zero]

theorem physicalNullHeight_on_closed_fiber (d : ℕ) (a : ℝ) (ha : 0 < a)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (ht : a ≤ ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖)
    (hr : OAI.Analysis.PDE.Green.physicalFullDefining d a x ≤ 0) : a ≤ ‖physicalNullHeight d x‖ := by
  apply (OAI.Analysis.Calculus.Current.fiber_collar_height_bounds a (physicalToNullCurrentPoint d x).2 ha _ _).1
  · rwa [imaginaryTime_physicalToNullCurrentPoint]
  · rw [physicalFullDefining_eq_null] at hr
    exact hr.trans (by norm_num)

def extendedPhysicalLatticeCurrent {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ) (ha : 0 < a)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) :=
  awayZeroExtension a ha (physicalNullHeight d) (physicalLatticeCurrent R h a κ cR cI v)

def extendedPhysicalBackground (d : ℕ) (a : ℝ) (ha : 0 < a) :=
  awayZeroExtension a ha (physicalNullHeight d) (physicalBackground d)

theorem contDiff_extendedPhysicalLatticeCurrent {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) :
    ContDiff ℝ ∞ (extendedPhysicalLatticeCurrent R h a ha κ cR cI v) := by
  apply contDiff_awayZeroExtension a ha (contDiff_physicalNullHeight d)
  intro x hx
  exact contDiffAt_physicalLatticeCurrent R h a hh κ cR cI v x hx

theorem contDiffAt_physicalBackground (d : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
    (hx : physicalNullHeight d x ≠ 0) : ContDiffAt ℝ ∞ (physicalBackground d) x := by
  have hc : ContDiff ℝ ∞ (fun x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 => (physicalToNullCurrentPoint d x).2) := by
    unfold physicalToNullCurrentPoint
    fun_prop
  exact (((OAI.Analysis.Calculus.Current.contDiffAt_phi_real _ hx).norm_sq ℂ).of_le (by simp)).comp x hc.contDiffAt

theorem contDiff_extendedPhysicalBackground (d : ℕ) (a : ℝ) (ha : 0 < a) :
    ContDiff ℝ ∞ (extendedPhysicalBackground d a ha) :=
  contDiff_awayZeroExtension a ha (contDiff_physicalNullHeight d)
    (contDiffAt_physicalBackground d)

/-- Both extensions agree on a full neighborhood of every point in every
closed physical fiber. Thus all differential identities there are preserved. -/
theorem extendedPhysical_fields_eq_near {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ) (ha : 0 < a)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
    (ht : a ≤ ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖) (hr : OAI.Analysis.PDE.Green.physicalFullDefining d a x ≤ 0) :
    extendedPhysicalLatticeCurrent R h a ha κ cR cI v =ᶠ[𝓝 x] physicalLatticeCurrent R h a κ cR cI v ∧
    extendedPhysicalBackground d a ha =ᶠ[𝓝 x] physicalBackground d := by
  have hy := physicalNullHeight_on_closed_fiber d a ha x ht hr
  exact ⟨awayZeroExtension_eq_near a ha (contDiff_physicalNullHeight d).continuous _ hy,
    awayZeroExtension_eq_near a ha (contDiff_physicalNullHeight d).continuous _ hy⟩

theorem extendedPhysicalBackground_periodic (d : ℕ) (a : ℝ) (ha : 0 < a)
    (y : OAI.Analysis.Calculus.Current.SpatialSpace d) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    extendedPhysicalBackground d a ha (x + physicalSpatialTranslate y) =
      extendedPhysicalBackground d a ha x := by
  apply awayZeroExtension_periodic a ha _ (physicalNullHeight_spatialTranslate d y) _ x
  intro x
  simp only [physicalBackground, physicalToNullCurrentPoint_add,
    physicalToNullCurrentPoint_spatialTranslate, Prod.snd_add, add_zero]

theorem extendedPhysicalLatticeCurrent_periodic {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ) (ha : 0 < a)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (i : Option (Fin d))
    (hfreq : ∀ j, ∃ k : ℤ, inner ℝ (packetSpatialFrequency (κ j) (v j))
      (R (EuclideanSpace.single i 1)) = (k : ℝ) * (2 * Real.pi) / 100)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    extendedPhysicalLatticeCurrent R h a ha κ cR cI v
      (x + physicalSpatialTranslate ((100 : ℝ) • R (EuclideanSpace.single i 1))) =
      extendedPhysicalLatticeCurrent R h a ha κ cR cI v x :=
  awayZeroExtension_periodic a ha _ (physicalNullHeight_spatialTranslate d _)
    (physicalLatticeCurrent_periodic_of_dual_lattice R h a κ cR cI v i hfreq) x

end OAI.Analysis.PDE.Concentration
