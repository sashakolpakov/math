import OAI.AlgebraicTopology.DeRham.Comparison.CubicalDegenerateIntegration
import OAI.AlgebraicTopology.DeRham.Comparison.StokesF
import OAI.Analysis.DifferentialForms.Manifold.Vectors
import OAI.AlgebraicTopology.DeRham.Comparison.DuffyCoordinates
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-! # Duffy Degenerate Faces -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DuffyDegenerateFaces.Duffy

noncomputable section

/-!
# Degenerate upper faces of the Duffy parametrization

The relevant degeneracy is an explicit missing cube coordinate. Vanishing
of the differential in that direction forces the genuine top-degree
alternating pullback to vanish, before integration.
-/

open Set OAI.AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes
open scoped ContDiff

/-- Once a non-final parameter is one, the vanishing remaining product makes
the Duffy polynomial independent of its last parameter. -/
theorem coordinates_update_last_of_one (n : ℕ) :
    ∀ (i : Fin n) (t : Fin (n + 1) → ℝ), t i.castSucc = 1 → ∀ r : ℝ,
      DuffyCoordinates.Duffy.coordinates (n + 1) (Function.update t (Fin.last n) r) = DuffyCoordinates.Duffy.coordinates (n + 1) t := by
  induction n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      intro i t hone r
      have hne : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by
        intro heq
        have hv := congrArg Fin.val heq
        simp only [Fin.val_zero, Fin.val_last] at hv
        omega
      cases i using Fin.cases with
      | zero =>
          change t 0 = 1 at hone
          simp only [DuffyCoordinates.Duffy.coordinates_succ, Function.update_of_ne hne, hone, sub_self, zero_mul]
      | succ j =>
          change Fin.tail t j.castSucc = 1 at hone
          change (Fin.cons ((Function.update t (Fin.last (n + 1)) r) 0)
              (fun k => (1 - (Function.update t (Fin.last (n + 1)) r) 0) *
                DuffyCoordinates.Duffy.coordinates (n + 1) (Fin.tail (Function.update t (Fin.last (n + 1)) r)) k) :
              Fin (n + 3) → ℝ) =
            (Fin.cons (t 0) (fun k => (1 - t 0) * DuffyCoordinates.Duffy.coordinates (n + 1) (Fin.tail t) k) :
              Fin (n + 3) → ℝ)
          have htail : Fin.tail (Function.update t (Fin.last (n + 1)) r) =
              Function.update (Fin.tail t) (Fin.last n) r :=
            Fin.tail_update_succ t (Fin.last n) r
          rw [Function.update_of_ne hne, htail, ih j (Fin.tail t) hone r]

/-- Every upper face except the final one ignores the last remaining cube coordinate. -/
theorem coordinates_insertNth_one_update_last (n : ℕ) (i : Fin (n + 1))
    (t : Fin (n + 1) → ℝ) (r : ℝ) :
    DuffyCoordinates.Duffy.coordinates (n + 2) (Fin.insertNth i.castSucc 1 (Function.update t (Fin.last n) r)) =
      DuffyCoordinates.Duffy.coordinates (n + 2) (Fin.insertNth i.castSucc 1 t) := by
  rw [Fin.insertNth_update, Fin.succAbove_ne_last_last (Fin.castSucc_ne_last i)]
  exact coordinates_update_last_of_one (n + 1) i (Fin.insertNth i.castSucc 1 t)
    (Fin.insertNth_apply_same _ _ _) r

/-- The same independence statement for an arbitrary explicitly non-final face index. -/
theorem coordinates_insertNth_one_update_last_of_ne_last (n : ℕ) (i : Fin (n + 2))
    (hi : i ≠ Fin.last (n + 1)) (t : Fin (n + 1) → ℝ) (r : ℝ) :
    DuffyCoordinates.Duffy.coordinates (n + 2) (Fin.insertNth i 1 (Function.update t (Fin.last n) r)) =
      DuffyCoordinates.Duffy.coordinates (n + 2) (Fin.insertNth i 1 t) := by
  obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
  exact coordinates_insertNth_one_update_last n j t r

/-- The actual globally polynomial Duffy map, packaged only as a smooth cube. -/
def coordinateCube (n : ℕ) : StokesF.SingularCubeStokes.SmoothSingularCube n (n + 1) where
  toFun := DuffyCoordinates.Duffy.coordinates n
  smooth := DuffyCoordinates.Duffy.contDiff_coordinates n ∞

/-- A non-final upper face of the actual Duffy cube. -/
def oneFaceCube (n : ℕ) (i : Fin (n + 1)) : StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) (n + 3) :=
  StokesF.SingularCubeStokes.singularFace (coordinateCube (n + 2)) i.castSucc 1

@[simp]
theorem oneFaceCube_apply (n : ℕ) (i : Fin (n + 1)) (t : Fin (n + 1) → ℝ) :
    oneFaceCube n i t = DuffyCoordinates.Duffy.coordinates (n + 2) (Fin.insertNth i.castSucc 1 t) := by
  rfl

theorem oneFaceCube_ignores_last (n : ℕ) (i : Fin (n + 1)) :
    CubicalDegeneracyOperators.IgnoresCoordinate (oneFaceCube n i) (Fin.last n) := by
  intro t r
  simp only [oneFaceCube_apply, coordinates_insertNth_one_update_last]

theorem oneFaceCube_isDegenerate (n : ℕ) (i : Fin (n + 1)) :
    CubicalDegeneracyOperators.IsDegenerateCube (oneFaceCube n i) :=
  ⟨Fin.last n, oneFaceCube_ignores_last n i⟩

/-- A smooth cube that ignores a coordinate has zero derivative in that
standard coordinate direction, by differentiating its constant coordinate-update path. -/
theorem fderiv_basis_eq_zero_of_ignoresCoordinate {n m : ℕ}
    (sigma : StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m) (i : Fin (n + 1))
    (hi : CubicalDegeneracyOperators.IgnoresCoordinate sigma i) (x : Fin (n + 1) → ℝ) :
    fderiv ℝ sigma.toFun x (Pi.single i 1) = 0 := by
  have hpath : HasDerivAt (Function.update x i) (Pi.single i 1) (x i) := by
    refine (hasFDerivAt_update (𝕜 := ℝ) (i := i) x (x i)).hasDerivAt.congr_deriv ?_
    ext a
    by_cases ha : a = i <;> simp [ha]
  have hdiff : HasFDerivAt sigma.toFun (fderiv ℝ sigma.toFun x)
      (Function.update x i (x i)) := by
    simpa using (sigma.smooth.differentiable (by simp)).differentiableAt.hasFDerivAt (x := x)
  have hchain := hdiff.comp_hasDerivAt (x i) hpath
  have hconstant : HasDerivAt (sigma.toFun ∘ Function.update x i) 0 (x i) := by
    have heq : sigma.toFun ∘ Function.update x i = fun _ => sigma x := by
      funext r
      exact hi x r
    rw [heq]
    exact hasDerivAt_const (x i) (sigma x)
  exact hchain.unique hconstant

/-- An explicit zero column annihilates a top-degree alternating pullback.
The proof evaluates on distinct standard basis vectors and uses alternation. -/
theorem alternating_comp_eq_zero_of_basis_kernel {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : (Fin d → ℝ) →L[ℝ] F) (i : Fin d) (hi : L (Pi.single i 1) = 0)
    (omega : F [⋀^Fin d]→L[ℝ] ℂ) :
    omega.compContinuousLinearMap L = 0 := by
  have hz : (omega.compContinuousLinearMap L).toAlternatingMap = 0 := by
    apply (Pi.basisFun ℝ (Fin d)).ext_alternating
    intro a ha
    obtain ⟨j, hj⟩ := (Finite.surjective_of_injective ha) i
    change omega (fun k => L ((Pi.basisFun ℝ (Fin d)) (a k))) = 0
    apply omega.map_coord_zero j
    simpa only [hj, Pi.basisFun_apply] using hi
  ext v
  exact congrArg (fun f : (Fin d → ℝ) [⋀^Fin d]→ₗ[ℝ] ℂ => f v) hz

/-- Every actual top-degree covector pulls back to zero along a smooth cube
with the stated concrete coordinate independence. -/
theorem pullback_eq_zero_of_ignoresCoordinate {n m : ℕ}
    (sigma : StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m) (i : Fin (n + 1))
    (hi : CubicalDegeneracyOperators.IgnoresCoordinate sigma i) (x : Fin (n + 1) → ℝ)
    (omega : (Fin m → ℝ) [⋀^Fin (n + 1)]→L[ℝ] ℂ) :
    omega.compContinuousLinearMap (fderiv ℝ sigma.toFun x) = 0 :=
  alternating_comp_eq_zero_of_basis_kernel _ i
    (fderiv_basis_eq_zero_of_ignoresCoordinate sigma i hi x) omega

/-- The final remaining standard direction maps to zero on every non-final
upper Duffy face, by the proved coordinate independence. -/
theorem fderiv_oneFaceCube_last (n : ℕ) (i : Fin (n + 1)) (t : Fin (n + 1) → ℝ) :
    fderiv ℝ (oneFaceCube n i).toFun t (Pi.single (Fin.last n) 1) = 0 :=
  fderiv_basis_eq_zero_of_ignoresCoordinate (oneFaceCube n i) (Fin.last n)
    (oneFaceCube_ignores_last n i) t

/-- The whole top-degree alternating pullback vanishes on a non-final upper
Duffy face. No extension of a simplex map or of a form is needed for this
pointwise statement about the actual covector at the image point. -/
theorem oneFaceCube_pullback_eq_zero (n : ℕ) (i : Fin (n + 1))
    (t : Fin (n + 1) → ℝ)
    (omega : (Fin (n + 3) → ℝ) [⋀^Fin (n + 1)]→L[ℝ] ℂ) :
    omega.compContinuousLinearMap (fderiv ℝ (oneFaceCube n i).toFun t) = 0 :=
  pullback_eq_zero_of_ignoresCoordinate (oneFaceCube n i) (Fin.last n)
    (oneFaceCube_ignores_last n i) t omega

/-- The actual bundled pullback of a smooth top-degree form is the zero form. -/
theorem smoothForm_pullback_oneFaceCube (n : ℕ) (i : Fin (n + 1))
    (form : OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm (Fin (n + 3) → ℝ) (n + 1)) :
    OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback (oneFaceCube n i).toFun (oneFaceCube n i).smooth form = 0 := by
  apply OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
  intro t
  exact oneFaceCube_pullback_eq_zero n i t (form (oneFaceCube n i t))

/-- In particular the actual complex integration coefficient vanishes. -/
@[simp]
theorem complexCubeIntegrand_oneFaceCube (n : ℕ) (i : Fin (n + 1))
    (form : OAI.Analysis.DifferentialForms.Manifold.Basic.RawForm (Fin (n + 3) → ℝ) (n + 1)) (t : Fin (n + 1) → ℝ) :
    ComplexCubeIntegration.complexCubeIntegrand (oneFaceCube n i) form t = 0 := by
  exact (form (oneFaceCube n i t)).map_coord_zero (Fin.last n)
    (fderiv_oneFaceCube_last n i t)

/-- The genuine differential-form integral over each degenerate upper face is zero. -/
@[simp]
theorem complexIntegrateForm_oneFaceCube (n : ℕ) (i : Fin (n + 1))
    (form : OAI.Analysis.DifferentialForms.Manifold.Basic.RawForm (Fin (n + 3) → ℝ) (n + 1)) :
    ComplexCubeIntegration.complexIntegrateForm (oneFaceCube n i) form = 0 := by
  obtain ⟨tau, j, heq⟩ := (CubicalDegeneracyOperators.isDegenerateCube_iff (oneFaceCube n i)).mp
    (oneFaceCube_isDegenerate n i)
  rw [← heq]
  exact CubicalDegenerateIntegration.complexIntegrateForm_cubeDegeneracy tau j form

end

end OAI.AlgebraicTopology.DeRham.Comparison.DuffyDegenerateFaces.Duffy
