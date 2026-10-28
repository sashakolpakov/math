import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas

/-! # Simplex Face Identities -/

namespace OAI.AlgebraicTopology.Products.SimplexFaceIdentities

noncomputable section

section

/-!
# The front and back restrictions of an actual singular simplex

These operations are the restrictions along the standard monotone inclusions
of vertices. They are defined for every simplicial set, hence in particular
for mathlib's actual singular simplicial set. The face identities are proved
as equalities of maps in the simplex category before applying the functor.
-/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

open _root_.CategoryTheory Opposite
open scoped Simplicial

/-- Transport a simplex across an equality of its dimensions. -/
def simplexCast (K : SSet.{0}) {m n : ℕ} (h : m = n) (s : K _⦋m⦌) : K _⦋n⦌ := h ▸ s

@[simp]
theorem simplexCast_rfl (K : SSet.{0}) {n : ℕ} (s : K _⦋n⦌) :
    simplexCast K rfl s = s := rfl

/-- Restriction to the consecutive vertices `a,..., a + p`. -/
def intervalFace (K : SSet.{0}) {n : ℕ} (a p : ℕ) (h : a + p ≤ n) :
    K _⦋n⦌ → K _⦋p⦌ :=
  K.map (SimplexCategory.subinterval a p h).op

/-- The vertex inclusion `0,..., p` into `0,..., p + q`. -/
def frontInclusion (p q : ℕ) : ⦋p⦌ ⟶ ⦋p + q⦌ :=
  SimplexCategory.subinterval 0 p (by omega)

/-- The vertex inclusion `p,..., p + q` into `0,..., p + q`. -/
def backInclusion (p q : ℕ) : ⦋q⦌ ⟶ ⦋p + q⦌ :=
  SimplexCategory.subinterval p q le_rfl

/-- The front `p`-face in the Alexander--Whitney cut of a `(p + q)`-simplex. -/
def frontFace (K : SSet.{0}) (p q : ℕ) : K _⦋p + q⦌ → K _⦋p⦌ :=
  intervalFace K 0 p (by omega)

/-- The back `q`-face, sharing vertex `p` with the front face. -/
def backFace (K : SSet.{0}) (p q : ℕ) : K _⦋p + q⦌ → K _⦋q⦌ :=
  intervalFace K p q le_rfl

theorem frontFace_def (K : SSet.{0}) (p q : ℕ) :
    frontFace K p q = K.map (frontInclusion p q).op := rfl

theorem backFace_def (K : SSet.{0}) (p q : ℕ) :
    backFace K p q = K.map (backInclusion p q).op := rfl

@[simp]
theorem frontInclusion_apply (p q : ℕ) (i : Fin (p + 1)) :
    ((frontInclusion p q).toOrderHom i).val = i.val := by
  simp [frontInclusion, SimplexCategory.subinterval]

@[simp]
theorem backInclusion_apply (p q : ℕ) (i : Fin (q + 1)) :
    ((backInclusion p q).toOrderHom i).val = i.val + p := rfl

@[simp]
theorem intervalFace_simplexCast (K : SSet.{0}) {m n : ℕ} (e : m = n)
    (a p : ℕ) (h : a + p ≤ n) (s : K _⦋m⦌) :
    intervalFace K a p h (simplexCast K e s) =
      intervalFace K a p (by omega) s := by
  subst n
  rfl

/-- Restrictions commute with every map of simplicial sets. -/
theorem intervalFace_naturality {K L : SSet.{0}} (f : K ⟶ L)
    {n : ℕ} (a p : ℕ) (h : a + p ≤ n) (s : K _⦋n⦌) :
    intervalFace L a p h (f.app _ s) = f.app _ (intervalFace K a p h s) := by
  exact (f.naturality_apply (SimplexCategory.subinterval a p h).op s).symm

theorem frontFace_naturality {K L : SSet.{0}} (f : K ⟶ L)
    (p q : ℕ) (s : K _⦋p + q⦌) :
    frontFace L p q (f.app _ s) = f.app _ (frontFace K p q s) :=
  intervalFace_naturality f 0 p (by omega) s

theorem backFace_naturality {K L : SSet.{0}} (f : K ⟶ L)
    (p q : ℕ) (s : K _⦋p + q⦌) :
    backFace L p q (f.app _ s) = f.app _ (backFace K p q s) :=
  intervalFace_naturality f p q le_rfl s

/-- The indices of faces deleting one of the vertices `0,..., p`. -/
def leftFaceIndex (p q : ℕ) (i : Fin (p + 1)) : Fin (p + q + 2) :=
  ⟨i.val, by omega⟩

/-- The indices of faces deleting one of the vertices `p + 1,..., p + q + 1`. -/
def rightFaceIndex (p q : ℕ) (i : Fin (q + 1)) : Fin (p + q + 2) :=
  ⟨p + 1 + i.val, by omega⟩

@[simp]
theorem leftFaceIndex_val (p q : ℕ) (i : Fin (p + 1)) :
    (leftFaceIndex p q i).val = i.val := rfl

@[simp]
theorem rightFaceIndex_val (p q : ℕ) (i : Fin (q + 1)) :
    (rightFaceIndex p q i).val = p + 1 + i.val := rfl

/-- Split the complete boundary index set at the Alexander--Whitney cut. -/
theorem sum_face_split {M : Type*} [AddCommMonoid M] (p q : ℕ)
    (f : Fin (p + q + 2) → M) :
    (∑ i, f i) = (∑ i : Fin (p + 1), f (leftFaceIndex p q i)) +
      ∑ i : Fin (q + 1), f (rightFaceIndex p q i) := by
  let e : (p + 1) + (q + 1) = p + q + 2 := by omega
  calc
    (∑ i, f i) = ∑ i : Fin ((p + 1) + (q + 1)), f (i.cast e) :=
      (Fin.sum_congr' f e).symm
    _ = _ := by
      rw [Fin.sum_univ_add]
      rfl

/-- The continuous map of standard simplices induced by an interval of vertices. -/
def standardSimplexInterval {n : ℕ} (a p : ℕ) (h : a + p ≤ n) :
    C(Convexity.StdSimplex ℝ (Fin (p + 1)), Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  ⟨Convexity.StdSimplex.map (SimplexCategory.subinterval a p h),
    Convexity.StdSimplex.continuous_map ℝ (SimplexCategory.subinterval a p h)⟩

/-- On actual singular simplices, interval restriction is precomposition
with the stated continuous inclusion of topological standard simplices. -/
theorem intervalFace_continuousMap (X : TopCat.{0}) {n : ℕ} (a p : ℕ)
    (h : a + p ≤ n) (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    X.toSSetObjEquiv (op ⦋p⦌) (intervalFace (TopCat.toSSet.obj X) a p h s) =
      (X.toSSetObjEquiv (op ⦋n⦌) s).comp (standardSimplexInterval a p h) := by
  ext z
  exact TopCat.toSSetObjEquiv_naturality_apply (SimplexCategory.subinterval a p h) s z

end

/-!
# Boundary faces and the Alexander--Whitney cut

The two groups of boundary faces are the actual monotone vertex inclusions.
The last face of the front restriction and the first face of the back
restriction give the same middle cut, which supplies the cancellation in the
cup-product Leibniz rule.
-/

open _root_.CategoryTheory Opposite
open scoped Simplicial

theorem frontInclusion_comp_delta_left (p q : ℕ) (i : Fin (p + 1)) :
    frontInclusion p q ≫ SimplexCategory.δ (leftFaceIndex p q i) =
      SimplexCategory.δ i.castSucc ≫
        SimplexCategory.subinterval 0 (p + 1) (by omega : 0 + (p + 1) ≤ p + q + 1) := by
  ext k
  have hk : k.val < p + 1 := k.isLt
  change ((leftFaceIndex p q i).succAbove (⟨k.val, by omega⟩ : Fin (p + q + 1))).val =
    (i.castSucc.succAbove k).val
  simp only [leftFaceIndex, Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> rfl

theorem backInclusion_comp_delta_left (p q : ℕ) (i : Fin (p + 1)) :
    backInclusion p q ≫ SimplexCategory.δ (leftFaceIndex p q i) =
      SimplexCategory.subinterval (p + 1) q (by omega : (p + 1) + q ≤ p + q + 1) := by
  ext k
  have hk : k.val < q + 1 := k.isLt
  change ((leftFaceIndex p q i).succAbove (⟨k.val + p, by omega⟩ : Fin (p + q + 1))).val =
    k.val + (p + 1)
  have hi : ¬k.val + p < i.val := by omega
  simp [leftFaceIndex, Fin.succAbove, Fin.lt_def, hi, Nat.add_assoc]

theorem frontInclusion_comp_delta_right (p q : ℕ) (i : Fin (q + 1)) :
    frontInclusion p q ≫ SimplexCategory.δ (rightFaceIndex p q i) =
      SimplexCategory.subinterval 0 p (by omega : 0 + p ≤ p + q + 1) := by
  ext k
  have hk : k.val < p + 1 := k.isLt
  change ((rightFaceIndex p q i).succAbove (⟨k.val, by omega⟩ : Fin (p + q + 1))).val = k.val
  have hi : k.val < p + 1 + i.val := by omega
  simp [rightFaceIndex, Fin.succAbove, Fin.lt_def, hi]

theorem backInclusion_comp_delta_right (p q : ℕ) (i : Fin (q + 1)) :
    backInclusion p q ≫ SimplexCategory.δ (rightFaceIndex p q i) =
      SimplexCategory.δ i.succ ≫
        SimplexCategory.subinterval p (q + 1) (by omega : p + (q + 1) ≤ p + q + 1) := by
  ext k
  have hk : k.val < q + 1 := k.isLt
  change ((rightFaceIndex p q i).succAbove (⟨k.val + p, by omega⟩ : Fin (p + q + 1))).val =
    (i.succ.succAbove k).val + p
  simp only [rightFaceIndex, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ]
  split_ifs <;> simp only [Fin.val_castSucc, Fin.val_succ] <;> omega

theorem delta_last_comp_frontInterval (p q : ℕ) :
    SimplexCategory.δ (Fin.last (p + 1)) ≫
        SimplexCategory.subinterval 0 (p + 1) (by omega : 0 + (p + 1) ≤ p + q + 1) =
      SimplexCategory.subinterval 0 p (by omega : 0 + p ≤ p + q + 1) := by
  ext k
  have hk : k.val ≤ p := Nat.lt_succ_iff.mp k.isLt
  change ((Fin.last (p + 1)).succAbove k).val = k.val
  simp [Fin.succAbove, Fin.lt_def, hk]

theorem delta_zero_comp_backInterval (p q : ℕ) :
    SimplexCategory.δ (0 : Fin (q + 2)) ≫
        SimplexCategory.subinterval p (q + 1) (by omega : p + (q + 1) ≤ p + q + 1) =
      SimplexCategory.subinterval (p + 1) q (by omega : (p + 1) + q ≤ p + q + 1) := by
  ext k
  change ((0 : Fin (q + 2)).succAbove k).val + p = k.val + (p + 1)
  simp [Fin.succAbove, Nat.add_comm, Nat.add_left_comm]

/-- Deleting a vertex on the front side restricts to that front boundary face. -/
theorem frontFace_delta_left (K : SSet.{0}) (p q : ℕ) (i : Fin (p + 1))
    (s : K _⦋p + q + 1⦌) :
    frontFace K p q (K.δ (leftFaceIndex p q i) s) =
      K.δ i.castSucc (frontFace K (p + 1) q
        (simplexCast K (by omega : p + q + 1 = (p + 1) + q) s)) := by
  simp only [frontFace, intervalFace_simplexCast]
  simpa only [frontInclusion, op_comp, Functor.map_comp, types_comp_apply,
    intervalFace, SimplicialObject.δ] using
    congrArg (fun f : ⦋p⦌ ⟶ ⦋p + q + 1⦌ => K.map f.op s)
      (frontInclusion_comp_delta_left p q i)

/-- Deleting a front vertex leaves the back restriction unchanged. -/
theorem backFace_delta_left (K : SSet.{0}) (p q : ℕ) (i : Fin (p + 1))
    (s : K _⦋p + q + 1⦌) :
    backFace K p q (K.δ (leftFaceIndex p q i) s) =
      backFace K (p + 1) q
        (simplexCast K (by omega : p + q + 1 = (p + 1) + q) s) := by
  simp only [backFace, intervalFace_simplexCast]
  simpa only [backInclusion, op_comp, Functor.map_comp, types_comp_apply,
    intervalFace, SimplicialObject.δ] using
    congrArg (fun f : ⦋q⦌ ⟶ ⦋p + q + 1⦌ => K.map f.op s)
      (backInclusion_comp_delta_left p q i)

/-- Deleting a back vertex leaves the front restriction unchanged. -/
theorem frontFace_delta_right (K : SSet.{0}) (p q : ℕ) (i : Fin (q + 1))
    (s : K _⦋p + q + 1⦌) :
    frontFace K p q (K.δ (rightFaceIndex p q i) s) = frontFace K p (q + 1) s := by
  simpa only [frontInclusion, frontFace, op_comp, Functor.map_comp, types_comp_apply,
    intervalFace, SimplicialObject.δ] using
    congrArg (fun f : ⦋p⦌ ⟶ ⦋p + q + 1⦌ => K.map f.op s)
      (frontInclusion_comp_delta_right p q i)

/-- Deleting a back vertex restricts to the corresponding back boundary face. -/
theorem backFace_delta_right (K : SSet.{0}) (p q : ℕ) (i : Fin (q + 1))
    (s : K _⦋p + q + 1⦌) :
    backFace K p q (K.δ (rightFaceIndex p q i) s) =
      K.δ i.succ (backFace K p (q + 1) s) := by
  simpa only [backInclusion, backFace, op_comp, Functor.map_comp, types_comp_apply,
    intervalFace, SimplicialObject.δ] using
    congrArg (fun f : ⦋q⦌ ⟶ ⦋p + q + 1⦌ => K.map f.op s)
      (backInclusion_comp_delta_right p q i)

/-- The last boundary face of the larger front face is the smaller front face. -/
theorem frontFace_delta_last (K : SSet.{0}) (p q : ℕ) (s : K _⦋p + q + 1⦌) :
    K.δ (Fin.last (p + 1)) (frontFace K (p + 1) q
      (simplexCast K (by omega : p + q + 1 = (p + 1) + q) s)) =
        frontFace K p (q + 1) s := by
  simp only [frontFace, intervalFace_simplexCast]
  simpa only [op_comp, Functor.map_comp, types_comp_apply,
    intervalFace, SimplicialObject.δ] using
    congrArg (fun f : ⦋p⦌ ⟶ ⦋p + q + 1⦌ => K.map f.op s)
      (delta_last_comp_frontInterval p q)

/-- The first boundary face of the larger back face is the smaller back face. -/
theorem backFace_delta_zero (K : SSet.{0}) (p q : ℕ) (s : K _⦋p + q + 1⦌) :
    K.δ (0 : Fin (q + 2)) (backFace K p (q + 1) s) =
      backFace K (p + 1) q
        (simplexCast K (by omega : p + q + 1 = (p + 1) + q) s) := by
  simp only [backFace, intervalFace_simplexCast]
  simpa only [op_comp, Functor.map_comp, types_comp_apply,
    intervalFace, SimplicialObject.δ] using
    congrArg (fun f : ⦋q⦌ ⟶ ⦋p + q + 1⦌ => K.map f.op s)
      (delta_zero_comp_backInterval p q)

end

end OAI.AlgebraicTopology.Products.SimplexFaceIdentities
