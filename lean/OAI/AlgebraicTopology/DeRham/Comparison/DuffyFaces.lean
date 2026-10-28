import OAI.AlgebraicTopology.DeRham.Comparison.DuffyCoordinates
import OAI.AlgebraicTopology.DeRham.Comparison.CubicalSupport
import Mathlib.Tactic.FinCases

/-! # Duffy Faces -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DuffyFaces.Duffy

/-!
# Nondegenerate faces of the recursive Duffy map

Setting cube coordinate `i` to zero inserts a zero in barycentric coordinate
`i`. Setting the final cube coordinate to one inserts a zero in the final
barycentric coordinate. These are identities of the actual polynomial maps
on all real inputs, and they induce the corresponding standard-simplex
cofaces on the closed unit cube.
-/

open OAI.AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

private theorem mul_insertNth_zero {n : ℕ} (a : ℝ) (i : Fin (n + 1))
    (v : Fin n → ℝ) :
    (fun j => a * Fin.insertNth (α := fun _ => ℝ) i 0 v j) =
      Fin.insertNth (α := fun _ => ℝ) i 0 (fun j => a * v j) := by
  funext j
  induction j using Fin.succAboveCases i with
  | x => simp
  | p j => simp

/-- Every zero cube face is the corresponding simplex coface in actual
barycentric coordinates. -/
theorem coordinates_insertNth_zero {n : ℕ} (i : Fin (n + 1)) (t : Fin n → ℝ) :
    DuffyCoordinates.Duffy.coordinates (n + 1) (Fin.insertNth (α := fun _ => ℝ) i 0 t) =
      Fin.insertNth (α := fun _ => ℝ) i.castSucc 0 (DuffyCoordinates.Duffy.coordinates n t) := by
  induction n with
  | zero =>
      have hi : i = 0 := Fin.ext (by omega)
      subst i
      change DuffyCoordinates.Duffy.coordinates 1 (Fin.insertNth (α := fun _ => ℝ) 0 0 t) = Fin.insertNth (α := fun _ => ℝ) 0 0 (DuffyCoordinates.Duffy.coordinates 0 t)
      simp only [Fin.insertNth_zero', DuffyCoordinates.Duffy.coordinates_succ_cons, sub_zero, one_mul]
  | succ n ih =>
      refine Fin.cases ?_ (fun i => ?_) i
      · change DuffyCoordinates.Duffy.coordinates (n + 2) (Fin.insertNth (α := fun _ => ℝ) 0 0 t) =
          Fin.insertNth (α := fun _ => ℝ) 0 0 (DuffyCoordinates.Duffy.coordinates (n + 1) t)
        simp only [Fin.insertNth_zero', DuffyCoordinates.Duffy.coordinates_succ_cons, sub_zero, one_mul]
      · have ht : Fin.insertNth (α := fun _ => ℝ) i.succ (0 : ℝ) t =
            Fin.cons (t 0) (Fin.insertNth (α := fun _ => ℝ) i 0 (Fin.tail t)) := by
          simpa only [Fin.cons_self_tail] using
            (Fin.insertNth_succ_cons i 0 (t 0) (Fin.tail t))
        rw [ht, DuffyCoordinates.Duffy.coordinates_succ_cons, DuffyCoordinates.Duffy.coordinates_succ n t]
        change Fin.cons (t 0)
            (fun j => (1 - t 0) * DuffyCoordinates.Duffy.coordinates (n + 1) (Fin.insertNth (α := fun _ => ℝ) i 0 (Fin.tail t)) j) =
          Fin.insertNth (α := fun _ => ℝ) i.castSucc.succ 0
            (Fin.cons (t 0) (fun j => (1 - t 0) * DuffyCoordinates.Duffy.coordinates n (Fin.tail t) j))
        rw [Fin.insertNth_succ_cons, ih i (Fin.tail t)]
        exact congrArg (Fin.cons (α := fun _ => ℝ) (t 0))
          (mul_insertNth_zero (1 - t 0) i.castSucc (DuffyCoordinates.Duffy.coordinates n (Fin.tail t)))

/-- The final upper cube face is the final simplex coface. -/
theorem coordinates_insertNth_last_one {n : ℕ} (t : Fin n → ℝ) :
    DuffyCoordinates.Duffy.coordinates (n + 1) (Fin.insertNth (α := fun _ => ℝ) (Fin.last n) 1 t) =
      Fin.insertNth (α := fun _ => ℝ) (Fin.last (n + 1)) 0 (DuffyCoordinates.Duffy.coordinates n t) := by
  induction n with
  | zero =>
      change DuffyCoordinates.Duffy.coordinates 1 (Fin.insertNth (α := fun _ => ℝ) 0 1 t) =
        Fin.insertNth (α := fun _ => ℝ) (Fin.last 1) 0 (DuffyCoordinates.Duffy.coordinates 0 t)
      rw [Fin.insertNth_zero', DuffyCoordinates.Duffy.coordinates_succ_cons, Fin.insertNth_last']
      funext j
      fin_cases j <;> simp
      change (0 : ℝ) = Fin.snoc (α := fun _ => ℝ) (DuffyCoordinates.Duffy.coordinates 0 t) 0 (Fin.last 1)
      rw [Fin.snoc_last]
  | succ n ih =>
      have ht : Fin.insertNth (α := fun _ => ℝ) (Fin.last (n + 1)) (1 : ℝ) t =
          Fin.cons (t 0) (Fin.insertNth (α := fun _ => ℝ) (Fin.last n) 1 (Fin.tail t)) := by
        simpa only [Fin.cons_self_tail, Fin.succ_last] using
          (Fin.insertNth_succ_cons (Fin.last n) 1 (t 0) (Fin.tail t))
      rw [ht, DuffyCoordinates.Duffy.coordinates_succ_cons, DuffyCoordinates.Duffy.coordinates_succ n t]
      change Fin.cons (t 0)
          (fun j => (1 - t 0) *
            DuffyCoordinates.Duffy.coordinates (n + 1) (Fin.insertNth (α := fun _ => ℝ) (Fin.last n) 1 (Fin.tail t)) j) =
        Fin.insertNth (α := fun _ => ℝ) (Fin.last (n + 1)).succ 0
          (Fin.cons (t 0) (fun j => (1 - t 0) * DuffyCoordinates.Duffy.coordinates n (Fin.tail t) j))
      rw [Fin.insertNth_succ_cons, ih (Fin.tail t)]
      exact congrArg (Fin.cons (α := fun _ => ℝ) (t 0))
        (mul_insertNth_zero (1 - t 0) (Fin.last (n + 1)) (DuffyCoordinates.Duffy.coordinates n (Fin.tail t)))

/-- The zero-face identity in the cube-face notation used by Stokes. -/
theorem coordinates_faceInclusion_zero {n : ℕ} (i : Fin (n + 1)) (t : Fin n → ℝ) :
    DuffyCoordinates.Duffy.coordinates (n + 1) (StokesF.SingularCubeStokes.faceInclusion i 0 t) =
      Fin.insertNth (α := fun _ => ℝ) i.castSucc 0 (DuffyCoordinates.Duffy.coordinates n t) := by
  exact coordinates_insertNth_zero i t

/-- The final-upper-face identity in the cube-face notation used by Stokes. -/
theorem coordinates_faceInclusion_last_one {n : ℕ} (t : Fin n → ℝ) :
    DuffyCoordinates.Duffy.coordinates (n + 1) (StokesF.SingularCubeStokes.faceInclusion (Fin.last n) 1 t) =
      Fin.insertNth (α := fun _ => ℝ) (Fin.last (n + 1)) 0 (DuffyCoordinates.Duffy.coordinates n t) := by
  exact coordinates_insertNth_last_one t

/-- The standard simplex coface is literally insertion of a zero
barycentric coordinate. -/
theorem simplexFace_eq_insertNth {n : ℕ} (i : Fin (n + 1))
    (s : Convexity.StdSimplex ℝ (Fin n)) :
    (Convexity.StdSimplex.map i.succAbove s : Fin (n + 1) → ℝ) =
      Fin.insertNth (α := fun _ => ℝ) i 0 (s : Fin n → ℝ) := by
  funext j
  induction j using Fin.succAboveCases i with
  | x =>
      change s.weights.mapDomain i.succAbove i = _
      rw [Finsupp.mapDomain_of_notMem_range _ _ (by simp)]
      simp
  | p j =>
      change s.weights.mapDomain i.succAbove (i.succAbove j) = _
      rw [Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective]
      simp

/-- On the actual closed cube, every zero face agrees with its genuine
standard-simplex coface. -/
theorem toSimplex_face_zero {n : ℕ} (i : Fin (n + 1)) (t : StokesF.SingularCubeStokes.unitCube n) :
    DuffyCoordinates.Duffy.toSimplex (n + 1)
        ⟨StokesF.SingularCubeStokes.faceInclusion i 0 t.val, CubicalSupport.faceInclusion_mem_unitCube i ⟨le_rfl, zero_le_one⟩ t.property⟩ =
      Convexity.StdSimplex.map i.castSucc.succAbove (DuffyCoordinates.Duffy.toSimplex n t) := by
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).injective
  change DuffyCoordinates.Duffy.coordinates (n + 1) (StokesF.SingularCubeStokes.faceInclusion i 0 t.val) =
    (Convexity.StdSimplex.map i.castSucc.succAbove (DuffyCoordinates.Duffy.toSimplex n t) : Fin (n + 2) → ℝ)
  rw [coordinates_faceInclusion_zero, simplexFace_eq_insertNth, DuffyCoordinates.Duffy.toSimplex_val]

/-- On the actual closed cube, the final upper face agrees with the final
standard-simplex coface. -/
theorem toSimplex_face_last_one {n : ℕ} (t : StokesF.SingularCubeStokes.unitCube n) :
    DuffyCoordinates.Duffy.toSimplex (n + 1)
        ⟨StokesF.SingularCubeStokes.faceInclusion (Fin.last n) 1 t.val,
          CubicalSupport.faceInclusion_mem_unitCube (Fin.last n) ⟨zero_le_one, le_rfl⟩ t.property⟩ =
      Convexity.StdSimplex.map (Fin.last (n + 1)).succAbove (DuffyCoordinates.Duffy.toSimplex n t) := by
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).injective
  change DuffyCoordinates.Duffy.coordinates (n + 1) (StokesF.SingularCubeStokes.faceInclusion (Fin.last n) 1 t.val) =
    (Convexity.StdSimplex.map (Fin.last (n + 1)).succAbove (DuffyCoordinates.Duffy.toSimplex n t) : Fin (n + 2) → ℝ)
  rw [coordinates_faceInclusion_last_one, simplexFace_eq_insertNth, DuffyCoordinates.Duffy.toSimplex_val]

/-- Each lower cube face has the negative of its simplex-face sign. -/
theorem zero_face_boundarySign {n : ℕ} (i : Fin (n + 1)) :
    StokesF.SingularCubeStokes.boundarySign i false = -((-1 : ℤ) ^ i.val) := by
  simp [StokesF.SingularCubeStokes.boundarySign, StokesF.Stokes.orientation, pow_succ]

/-- The surviving upper cube face also has the negative of its
corresponding final simplex-face sign. -/
theorem last_one_boundarySign (n : ℕ) :
    StokesF.SingularCubeStokes.boundarySign (Fin.last n) true = -((-1 : ℤ) ^ (n + 1)) := by
  simp [StokesF.SingularCubeStokes.boundarySign, StokesF.Stokes.orientation, pow_succ]

end OAI.AlgebraicTopology.DeRham.Comparison.DuffyFaces.Duffy
