import OAI.Analysis.Calculus.FiniteExtension.Halfspace.Extension.Glue
import OAI.Analysis.Calculus.FiniteExtension.Halfspace.Extension.Map

/-! Finite reflected Taylor series on the negative halfspace. -/

noncomputable section
open Set
open scoped BigOperators ContDiff
namespace OAI.Analysis.Calculus.FiniteExtension

open OAI.Analysis.Normed.Function.Sobolev OAI.Analysis.PDE.Schauder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem taylor_zero (N : ℕ) (s : Set E) :
    HasFTaylorSeriesUpToOn N (fun _ : E => (0 : F))
      (fun _ : E => (0 : FormalMultilinearSeries ℝ E F)) s := by
  constructor
  · intro x hx
    rfl
  · intro m hm x hx
    convert (hasFDerivAt_const (𝕜 := ℝ)
      (0 : ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F) x).hasFDerivWithinAt using 1
    ext v w
    rfl
  · intro m hm
    exact continuousOn_const

theorem taylor_const_smul {N : ℕ} {s : Set E} {f : E → F}
    {p : E → FormalMultilinearSeries ℝ E F}
    (hp : HasFTaylorSeriesUpToOn N f p s) (c : ℝ) :
    HasFTaylorSeriesUpToOn N (fun x => c • f x) (fun x m => c • p x m) s := by
  constructor
  · intro x hx
    change c • (p x 0).curry0 = c • f x
    rw [hp.zero_eq x hx]
  · intro m hm x hx
    convert (hp.fderivWithin m hm x hx).const_smul c using 1
    ext v w
    rfl
  · intro m hm
    exact (hp.cont m hm).const_smul c

theorem taylor_finset_sum {N : ℕ} {s : Set E} {ι : Type*} (t : Finset ι)
    (f : ι → E → F) (p : ι → E → FormalMultilinearSeries ℝ E F)
    (hp : ∀ i ∈ t, HasFTaylorSeriesUpToOn N (f i) (p i) s) :
    HasFTaylorSeriesUpToOn N (fun x => ∑ i ∈ t, f i x)
      (fun x m => ∑ i ∈ t, p i x m) s := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    refine (taylor_zero (F := F) N s).congr_series ?_ |>.congr ?_
    · intro m hm x hx
      simp
    · intro x hx
      simp
  | @insert i t hi ih =>
    have hh := (hp i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))
    refine (hh.congr ?_).congr_series ?_
    · intro x hx
      simp only [Finset.sum_insert hi, Pi.add_apply]
    · intro m hm x hx
      simp [Finset.sum_insert hi]
      rfl

def reflectedValue (N : ℕ) (ℓ : E →L[ℝ] ℝ) (ν : E) (f : E → F) (x : E) : F :=
  ∑ j : Fin N, OAI.Analysis.Normed.Function.Sobolev.reflectionCoefficient N j • f (reflectionLinear ℓ ν (OAI.Analysis.Normed.Function.Sobolev.reflectionNode j) x)

def reflectedTaylor (N : ℕ) (ℓ : E →L[ℝ] ℝ) (ν : E)
    (p : E → FormalMultilinearSeries ℝ E F) (x : E) : FormalMultilinearSeries ℝ E F :=
  fun m => ∑ j : Fin N, OAI.Analysis.Normed.Function.Sobolev.reflectionCoefficient N j •
    (p (reflectionLinear ℓ ν (OAI.Analysis.Normed.Function.Sobolev.reflectionNode j) x) m).compContinuousLinearMap
      (fun _ => reflectionLinear ℓ ν (OAI.Analysis.Normed.Function.Sobolev.reflectionNode j))

theorem reflectedTaylor_boundary {N m : ℕ} (hm : m < N)
    (ℓ : E →L[ℝ] ℝ) (ν : E) (p : E → FormalMultilinearSeries ℝ E F)
    {x : E} (hx : ℓ x = 0) : reflectedTaylor N ℓ ν p x m = p x m := by
  unfold reflectedTaylor
  simp_rw [reflectionLinear_boundary ℓ ν _ hx]
  exact reflectionLinear_jet_moments hm ℓ ν (p x m)

theorem reflectedTaylor_hasFTaylor {N : ℕ}
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1)
    (f : E → F) (p : E → FormalMultilinearSeries ℝ E F)
    (hp : HasFTaylorSeriesUpToOn N f p {x | 0 ≤ ℓ x}) :
    HasFTaylorSeriesUpToOn N (reflectedValue (N+1) ℓ ν f)
      (reflectedTaylor (N+1) ℓ ν p) {x | ℓ x ≤ 0} := by
  apply taylor_finset_sum
  intro j hj
  apply taylor_const_smul
  apply (hp.compContinuousLinearMap (reflectionLinear ℓ ν (OAI.Analysis.Normed.Function.Sobolev.reflectionNode j))).mono
  exact reflectionLinear_maps_negative ℓ ν hν (OAI.Analysis.Normed.Function.Sobolev.reflectionNode_negative j).le

/-- The actual finite-reflection function is globally Cᴺ.  Its input has
Taylor jets only on the closed positive halfspace. -/
theorem contDiff_finite_reflection {N : ℕ}
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1)
    (f : E → F) (p : E → FormalMultilinearSeries ℝ E F)
    (hp : HasFTaylorSeriesUpToOn N f p {x | 0 ≤ ℓ x}) :
    ContDiff ℝ N (OAI.Analysis.PDE.Schauder.levelGlue ℓ f (reflectedValue (N+1) ℓ ν f)) := by
  apply HasFTaylorSeriesUpTo.contDiff
  apply hasFTaylorSeriesUpTo_levelGlue ℓ ℓ.continuous f _ p _ hp
    (reflectedTaylor_hasFTaylor ℓ ν hν f p hp)
  intro m hm x hx
  exact (reflectedTaylor_boundary (by omega) ℓ ν p hx).symm

end OAI.Analysis.Calculus.FiniteExtension
