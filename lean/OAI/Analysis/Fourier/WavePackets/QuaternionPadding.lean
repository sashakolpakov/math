import OAI.Analysis.PDE.Green.FiberHessian
import OAI.Analysis.PDE.Concentration.CovarianceLocal
import OAI.Analysis.PDE.Concentration.Packet.Hessian

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.Analysis.PDE.Concentration
open scoped ContDiff Topology

/-- Forget the fourth real slot in every quaternionic coordinate. -/
def dropFourthLinear (m : ℕ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 →ₗ[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 where
  toFun x := WithLp.toLp 2 (fun i => x (i.1, i.2.castSucc))
  map_add' x y := by ext i; rfl
  map_smul' c x := by ext i; rfl

def dropFourth (m : ℕ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 :=
  (dropFourthLinear m).toContinuousLinearMap

/-- The zero-fourth-slot section of `dropFourth`. -/
def insertFourthLinear (m : ℕ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 →ₗ[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 where
  toFun x := WithLp.toLp 2 (fun i => Fin.lastCases 0 (fun a => x (i.1, a)) i.2)
  map_add' x y := by
    ext ⟨i, a⟩
    change Fin.lastCases (motive := fun _ => ℝ) 0 (fun b => x (i, b) + y (i, b)) a =
      Fin.lastCases (motive := fun _ => ℝ) 0 (fun b => x (i, b)) a +
        Fin.lastCases (motive := fun _ => ℝ) 0 (fun b => y (i, b)) a
    refine Fin.lastCases ?_ (fun a => ?_) a <;>
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc, add_zero]
  map_smul' c x := by
    ext ⟨i, a⟩
    change Fin.lastCases (motive := fun _ => ℝ) 0 (fun b => c * x (i, b)) a =
      c * Fin.lastCases (motive := fun _ => ℝ) 0 (fun b => x (i, b)) a
    refine Fin.lastCases ?_ (fun a => ?_) a <;>
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc, mul_zero]

def insertFourth (m : ℕ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 :=
  (insertFourthLinear m).toContinuousLinearMap

@[simp] theorem dropFourth_apply (m : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4) (i : Fin m) (a : Fin 3) :
    dropFourth m x (i, a) = x (i, a.castSucc) := rfl

@[simp] theorem insertFourth_castSucc (m : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3) (i : Fin m) (a : Fin 3) :
    insertFourth m x (i, a.castSucc) = x (i, a) := by
  change Fin.lastCases 0 (fun a => x (i, a)) a.castSucc = x (i, a)
  exact Fin.lastCases_castSucc a

@[simp] theorem insertFourth_last (m : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3) (i : Fin m) :
    insertFourth m x (i, Fin.last 3) = 0 := by
  change Fin.lastCases (motive := fun _ => ℝ) 0 (fun a => x (i, a)) (Fin.last 3) = 0
  exact Fin.lastCases_last

@[simp] theorem dropFourth_insertFourth (m : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3) :
    dropFourth m (insertFourth m x) = x := by ext ⟨i, a⟩; simp

@[simp] theorem dropFourth_coordinate_castSucc (m : ℕ) (i : Fin m) (a : Fin 3) :
    dropFourth m (OAI.Analysis.PDE.Dirichlet.coordinateVector (i, a.castSucc)) = OAI.Analysis.PDE.Dirichlet.coordinateVector (i, a) := by
  ext ⟨j, b⟩
  simp [OAI.Analysis.PDE.Dirichlet.coordinateVector, PiLp.single_apply]

@[simp] theorem dropFourth_coordinate_last (m : ℕ) (i : Fin m) :
    dropFourth m (OAI.Analysis.PDE.Dirichlet.coordinateVector (i, Fin.last 3)) = 0 := by
  ext ⟨j, b⟩
  simp only [dropFourth_apply, OAI.Analysis.PDE.Dirichlet.coordinateVector, PiLp.single_apply, Prod.mk.injEq,
    Fin.castSucc_ne_last, and_false, ite_false, PiLp.zero_apply]

@[simp] theorem fourSlots_castSucc (a : Fin 3) : OAI.Analysis.Calculus.Quaternion.fourSlots a.castSucc = OAI.Analysis.Calculus.Quaternion.threeSlots a := by
  fin_cases a <;> rfl

/-- Padding by an unused periodic fourth slot preserves the actual
quaternionic Hessian, with no dimensional normalization factor. -/
theorem quaternionHessian_dropFourth {m : ℕ} {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 → ℝ}
    (hf : ContDiff ℝ 2 f) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => f (dropFourth m y)) x =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots f (dropFourth m x) := by
  apply Matrix.ext
  intro i j
  simp only [OAI.Analysis.PDE.Dirichlet.quaternionHessian, OAI.Analysis.Calculus.Quaternion.hessianMap, OAI.Analysis.PDE.Dirichlet.realHessian,
    OAI.Analysis.PDE.Green.second_fderiv_comp_linear (dropFourth m) hf]
  rw [Fin.sum_univ_castSucc]
  simp only [dropFourth_coordinate_last, map_zero, zero_apply,
    zero_smul, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Fin.sum_univ_castSucc]
  simp only [dropFourth_coordinate_last, map_zero, zero_smul, add_zero,
    dropFourth_coordinate_castSucc, fourSlots_castSucc]

theorem quaternionHessian_dropFourth_at {m : ℕ} {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 → ℝ}
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4} (hf : ContDiffAt ℝ 2 f (dropFourth m x)) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => f (dropFourth m y)) x =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots f (dropFourth m x) := by
  obtain ⟨g, hg, heq⟩ := OAI.Analysis.PDE.Dirichlet.exists_contDiff_extension_near_point hf
  have heq' := heq.comp_tendsto (dropFourth m).continuous.continuousAt
  change (fun y => g (dropFourth m y)) =ᶠ[𝓝 x] (fun y => f (dropFourth m y)) at heq'
  rw [← OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.fourSlots heq', quaternionHessian_dropFourth hg,
    OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.threeSlots heq]

/-- Restricting a function independent of the dummy slot gives exactly
the three-slot Hessian. Independence can later be deduced from Dirichlet
uniqueness under translations in the extra periodic directions. -/
theorem quaternionHessian_insertFourth_of_independent {m : ℕ}
    {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 → ℝ} (hu : ContDiff ℝ 2 u)
    (hind : ∀ x, u x = u (insertFourth m (dropFourth m x))) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun z => u (insertFourth m z)) y =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (insertFourth m y) := by
  have hf : ContDiff ℝ 2 (fun z => u (insertFourth m z)) := hu.comp (insertFourth m).contDiff
  have hfun : (fun x => u (insertFourth m (dropFourth m x))) = u :=
    funext (fun x => (hind x).symm)
  have he := quaternionHessian_dropFourth hf (insertFourth m y)
  simp only [dropFourth_insertFourth] at he
  rw [hfun] at he
  exact he.symm

end OAI.Analysis.Fourier.WavePackets
