import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration
import OAI.AlgebraicTopology.DeRham.Comparison.CubePullbackLocality
import OAI.AlgebraicTopology.DeRham.Comparison.CubicalSupport
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration
import OAI.AlgebraicTopology.DeRham.Comparison.DuffyFaces
import OAI.AlgebraicTopology.DeRham.Comparison.DuffyDegenerateFaces
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmooth
import Mathlib.Algebra.BigOperators.Fin

/-! # Smooth Simplex Stokes -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexStokes

noncomputable section

/-!
# Stokes signs for the actual Duffy simplex parametrization

The nondegenerate lower cube faces are the first simplex faces. The final
upper cube face is the last simplex face; all other upper faces collapse.
Consequently the cubical boundary contributes minus the standard alternating
simplex boundary. Multiplication by (-1)^n in degree n gives the standard
simplicial Stokes orientation.
-/

open _root_.CategoryTheory Opposite Set OAI.AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex BigOperators Simplicial _root_.Manifold ContDiff

section BoundarySigns

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- The surviving Duffy faces give the negative of the standard simplex boundary. -/
theorem duffy_boundary_sum (n : ℕ) (face : Fin (n + 2) → A)
    (upper : Fin (n + 1) → A)
    (hupper : ∀ i, i ≠ Fin.last n → upper i = 0)
    (hlast : upper (Fin.last n) = face (Fin.last (n + 1))) :
    (∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val • (upper i - face i.castSucc)) =
      -(∑ j : Fin (n + 2), (-1 : ℝ) ^ j.val • face j) := by
  have hu : (∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val • upper i) =
      (-1 : ℝ) ^ n • face (Fin.last (n + 1)) := by
    rw [Finset.sum_eq_single (Fin.last n)]
    · rw [hlast]
      rfl
    · intro i _ hi
      rw [hupper i hi, smul_zero]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  simp only [smul_sub, Finset.sum_sub_distrib]
  rw [hu]
  conv_rhs => rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, pow_succ, mul_smul, neg_one_smul, smul_neg]
  abel

/-- The degreewise normalization (-1)^n converts the Duffy boundary to the usual signs. -/
theorem duffy_normalized_boundary_sum (n : ℕ) (face : Fin (n + 2) → A)
    (upper : Fin (n + 1) → A)
    (hupper : ∀ i, i ≠ Fin.last n → upper i = 0)
    (hlast : upper (Fin.last n) = face (Fin.last (n + 1))) :
    (-1 : ℝ) ^ (n + 1) •
        (∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val • (upper i - face i.castSucc)) =
      ∑ j : Fin (n + 2), (-1 : ℝ) ^ j.val • ((-1 : ℝ) ^ n • face j) := by
  rw [duffy_boundary_sum n face upper hupper hlast, pow_succ, mul_smul,
    neg_one_smul, neg_neg, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact smul_comm _ _ _

/-- Real orientation signs agree exactly with the integral signs of simplicial chains. -/
theorem real_neg_one_pow_smul_eq_int (n : ℕ) (value : A) :
    (-1 : ℝ) ^ n • value = (-1 : ℤ) ^ n • value := by
  induction n with
  | zero => simp only [pow_zero, one_smul]
  | succ n ih =>
      simp only [pow_succ, mul_smul, neg_one_smul, smul_neg]
      exact congrArg Neg.neg ih

end BoundarySigns

/-- Resetting one coordinate to zero preserves the closed unit cube. -/
theorem update_zero_mem_unitCube {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ StokesF.SingularCubeStokes.unitCube n) (i : Fin n) : Function.update x i 0 ∈ StokesF.SingularCubeStokes.unitCube n := by
  constructor
  · intro j
    by_cases hji : j = i
    · subst j
      simp
    · simpa only [Function.update_of_ne hji] using hx.1 j
  · intro j
    by_cases hji : j = i
    · subst j
      simp
    · simpa only [Function.update_of_ne hji] using hx.2 j

section ManifoldCubes

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Coordinate independence only on the closed cube already forces a top integral to vanish. -/
theorem manifoldCubeIntegration_zero_of_coordinate_reset {n : ℕ}
    (cube : ManifoldCubeIntegration.SmoothManifoldCube E M (n + 1)) (i : Fin (n + 1))
    (hreset : ∀ x ∈ StokesF.SingularCubeStokes.unitCube (n + 1), cube (Function.update x i 0) = cube x)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (n + 1)) : ManifoldCubeIntegration.manifoldCubeIntegration cube form = 0 := by
  let residual := ManifoldCubeIntegration.manifoldCubeFace cube i 0
  let restored := ManifoldCubeIntegration.manifoldCubeDegeneracy residual i
  have hlocal : EqOn restored.toFun cube.toFun (StokesF.SingularCubeStokes.unitCube (n + 1)) := by
    intro x hx
    change cube (Fin.insertNth (α := fun _ => ℝ) i 0 (Fin.removeNth i x)) = cube x
    rw [Fin.insertNth_removeNth]
    exact hreset x hx
  have hintegrals := CubePullbackLocality.manifoldCubeIntegration_congr restored cube hlocal form
  have hzero : ManifoldCubeIntegration.manifoldCubeIntegration restored form = 0 :=
    ManifoldCubeIntegration.manifoldCubeIntegration_degeneracy residual i form
  exact hintegrals.symm.trans hzero

end ManifoldCubes

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type} [TopologicalSpace M] [ChartedSpace E M]

/-- The native smooth singular face is the ordinary barycentric simplex face. -/
theorem manifoldSmoothSimplex_face_apply {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n + 1⦌)
    (j : Fin (n + 2)) (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (TopCat.of M).toSSetObjEquiv (op ⦋n⦌)
      (((Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet.δ j) sigma).val x =
      (TopCat.of M).toSSetObjEquiv (op ⦋n + 1⦌) sigma.val (Convexity.StdSimplex.map j.succAbove x) := rfl

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Each lower Duffy cube face integrates exactly as the corresponding smooth simplex face. -/
theorem manifoldSimplexCube_integral_face_zero {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n + 1⦌)
    (i : Fin (n + 1)) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    ManifoldCubeIntegration.manifoldCubeIntegration (ManifoldCubeIntegration.manifoldCubeFace (ManifoldSimplexCube.manifoldSimplexCube sigma) i 0) form =
      ManifoldCubeIntegration.manifoldCubeIntegration (ManifoldSimplexCube.manifoldSimplexCube
        (((Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet.δ i.castSucc) sigma)) form := by
  refine CubePullbackLocality.manifoldCubeIntegration_congr _ _ ?_ form
  intro x hx
  change ManifoldSimplexCube.manifoldSimplexCube sigma (StokesF.SingularCubeStokes.faceInclusion i 0 x) =
    ManifoldSimplexCube.manifoldSimplexCube
      (((Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet.δ i.castSucc) sigma) x
  rw [ManifoldSimplexCube.manifoldSimplexCube_apply sigma
    ⟨StokesF.SingularCubeStokes.faceInclusion i 0 x, CubicalSupport.faceInclusion_mem_unitCube i ⟨le_rfl, zero_le_one⟩ hx⟩,
    ManifoldSimplexCube.manifoldSimplexCube_apply _ ⟨x, hx⟩,
    DuffyFaces.Duffy.toSimplex_face_zero i ⟨x, hx⟩, manifoldSmoothSimplex_face_apply]

/-- The final upper Duffy face is the final standard simplex face, including dimension one. -/
theorem manifoldSimplexCube_integral_face_last_one {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n + 1⦌)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    ManifoldCubeIntegration.manifoldCubeIntegration (ManifoldCubeIntegration.manifoldCubeFace (ManifoldSimplexCube.manifoldSimplexCube sigma) (Fin.last n) 1) form =
      ManifoldCubeIntegration.manifoldCubeIntegration (ManifoldSimplexCube.manifoldSimplexCube
        (((Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet.δ
          (Fin.last (n + 1))) sigma)) form := by
  refine CubePullbackLocality.manifoldCubeIntegration_congr _ _ ?_ form
  intro x hx
  change ManifoldSimplexCube.manifoldSimplexCube sigma (StokesF.SingularCubeStokes.faceInclusion (Fin.last n) 1 x) =
    ManifoldSimplexCube.manifoldSimplexCube
      (((Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet.δ (Fin.last (n + 1))) sigma) x
  rw [ManifoldSimplexCube.manifoldSimplexCube_apply sigma
    ⟨StokesF.SingularCubeStokes.faceInclusion (Fin.last n) 1 x,
      CubicalSupport.faceInclusion_mem_unitCube (Fin.last n) ⟨zero_le_one, le_rfl⟩ hx⟩,
    ManifoldSimplexCube.manifoldSimplexCube_apply _ ⟨x, hx⟩,
    DuffyFaces.Duffy.toSimplex_face_last_one ⟨x, hx⟩, manifoldSmoothSimplex_face_apply]

/-- Every other upper Duffy face has a missing parameter direction and contributes zero. -/
theorem manifoldSimplexCube_integral_face_one_zero {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n + 1⦌)
    (i : Fin (n + 1)) (hi : i ≠ Fin.last n) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    ManifoldCubeIntegration.manifoldCubeIntegration (ManifoldCubeIntegration.manifoldCubeFace (ManifoldSimplexCube.manifoldSimplexCube sigma) i 1) form = 0 := by
  obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last hi
  subst i
  cases n with
  | zero => exact Fin.elim0 j
  | succ n =>
      apply manifoldCubeIntegration_zero_of_coordinate_reset
        (ManifoldCubeIntegration.manifoldCubeFace (ManifoldSimplexCube.manifoldSimplexCube sigma) j.castSucc 1) (Fin.last n) _ form
      intro x hx
      let a : StokesF.SingularCubeStokes.unitCube (n + 2) :=
        ⟨StokesF.SingularCubeStokes.faceInclusion j.castSucc 1 (Function.update x (Fin.last n) 0),
          CubicalSupport.faceInclusion_mem_unitCube j.castSucc ⟨zero_le_one, le_rfl⟩
            (update_zero_mem_unitCube hx (Fin.last n))⟩
      let b : StokesF.SingularCubeStokes.unitCube (n + 2) :=
        ⟨StokesF.SingularCubeStokes.faceInclusion j.castSucc 1 x,
          CubicalSupport.faceInclusion_mem_unitCube j.castSucc ⟨zero_le_one, le_rfl⟩ hx⟩
      have hsimplex : DuffyCoordinates.Duffy.toSimplex (n + 2) a = DuffyCoordinates.Duffy.toSimplex (n + 2) b := by
        apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 3))).injective
        change (DuffyCoordinates.Duffy.toSimplex (n + 2) a : Fin (n + 3) → ℝ) =
          (DuffyCoordinates.Duffy.toSimplex (n + 2) b : Fin (n + 3) → ℝ)
        rw [DuffyCoordinates.Duffy.toSimplex_val, DuffyCoordinates.Duffy.toSimplex_val]
        exact DuffyDegenerateFaces.Duffy.coordinates_insertNth_one_update_last n j x 0
      change ManifoldSimplexCube.manifoldSimplexCube sigma a.val = ManifoldSimplexCube.manifoldSimplexCube sigma b.val
      calc
        ManifoldSimplexCube.manifoldSimplexCube sigma a.val =
            (TopCat.of M).toSSetObjEquiv (op ⦋n + 2⦌) sigma.val
              (DuffyCoordinates.Duffy.toSimplex (n + 2) a) := ManifoldSimplexCube.manifoldSimplexCube_apply sigma a
        _ = (TopCat.of M).toSSetObjEquiv (op ⦋n + 2⦌) sigma.val
              (DuffyCoordinates.Duffy.toSimplex (n + 2) b) :=
          congrArg ((TopCat.of M).toSSetObjEquiv (op ⦋n + 2⦌) sigma.val) hsimplex
        _ = ManifoldSimplexCube.manifoldSimplexCube sigma b.val := (ManifoldSimplexCube.manifoldSimplexCube_apply sigma b).symm

/-- Stokes for the actual Duffy integral, with real orientation signs. -/
theorem smoothSimplexStokes_real {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n + 1⦌)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    SmoothSimplexIntegration.smoothSimplexIntegration sigma (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form) =
      ∑ j : Fin (n + 2), (-1 : ℝ) ^ j.val •
        SmoothSimplexIntegration.smoothSimplexIntegration
          (((Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet.δ j) sigma) form := by
  simp only [SmoothSimplexIntegration.smoothSimplexIntegration_apply]
  rw [ManifoldCubeIntegration.manifoldCubeStokes]
  simp only [manifoldSimplexCube_integral_face_zero]
  exact duffy_normalized_boundary_sum n
    (fun j => ManifoldCubeIntegration.manifoldCubeIntegration (ManifoldSimplexCube.manifoldSimplexCube
      (((Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet.δ j) sigma)) form)
    (fun i => ManifoldCubeIntegration.manifoldCubeIntegration (ManifoldCubeIntegration.manifoldCubeFace (ManifoldSimplexCube.manifoldSimplexCube sigma) i 1) form)
    (fun i hi => manifoldSimplexCube_integral_face_one_zero sigma i hi form)
    (manifoldSimplexCube_integral_face_last_one sigma form)

/-- The actual simplex integral satisfies precisely the alternating coboundary of smooth
singular cochains, with no extra orientation or normalization premise. -/
theorem smoothSimplexStokes {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n + 1⦌)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    SmoothSimplexIntegration.smoothSimplexIntegration sigma (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
        SmoothSimplexIntegration.smoothSimplexIntegration
          (((Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet.δ j) sigma) form := by
  rw [smoothSimplexStokes_real]
  apply Finset.sum_congr rfl
  intro j _
  exact real_neg_one_pow_smul_eq_int j.val _

end

end OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexStokes
