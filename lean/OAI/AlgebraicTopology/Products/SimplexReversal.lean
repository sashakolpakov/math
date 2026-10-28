import OAI.AlgebraicTopology.Products.SimplexFaceIdentities
import Mathlib.Data.Fin.Rev
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-! # Simplex Reversal -/

namespace OAI.AlgebraicTopology.Products.SimplexReversal

noncomputable section

section

/-!
# Reversal of actual topological and singular simplices

The reversal of barycentric coordinates is the restriction of a continuous
linear map on the ambient coordinate space. It is not a morphism in the
simplex category. Its interaction with faces is proved as an equality of
continuous maps before passing to actual singular simplices.
-/

open _root_.CategoryTheory Opposite
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The continuous linear map inducing reversal of barycentric coordinates. -/
def simplexReversalLinear (n : ℕ) :
    (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ⟨FunOnFinite.linearMap ℝ ℝ Fin.rev,
    FunOnFinite.continuous_linearMap ℝ ℝ Fin.rev⟩

/-- The actual continuous affine involution reversing all vertices. -/
def simplexReversal (n : ℕ) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  ⟨Convexity.StdSimplex.map Fin.rev, Convexity.StdSimplex.continuous_map ℝ Fin.rev⟩

theorem simplexReversal_apply (n : ℕ) (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    simplexReversal n x = Convexity.StdSimplex.map Fin.rev x := rfl

/-- Reversal is the restriction of the displayed linear map, hence is affine. -/
theorem simplexReversal_linear_extension (n : ℕ)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (simplexReversal n x : Fin (n + 1) → ℝ) = simplexReversalLinear n x :=
  Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.map_coordinates Fin.rev x

/-- The coordinate at vertex `i` becomes the coordinate at the reversed vertex. -/
@[simp]
theorem simplexReversal_coordinate (n : ℕ)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    simplexReversal n x i = x i.rev := by
  change (Convexity.StdSimplex.map Fin.rev x).weights i = x.weights i.rev
  rw [Convexity.StdSimplex.weights_map]
  simpa only [Fin.rev_rev] using
    (Finsupp.mapDomain_apply_of_injective Fin.rev_injective x.weights i.rev)

@[simp]
theorem simplexReversal_vertex (n : ℕ) (i : Fin (n + 1)) :
    simplexReversal n (Convexity.StdSimplex.single i) = Convexity.StdSimplex.single i.rev :=
  Convexity.StdSimplex.map_single i Fin.rev

theorem simplexReversal_involutive (n : ℕ) :
    Function.Involutive (simplexReversal n) := by
  intro x
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).injective
  funext i
  simp

@[simp]
theorem simplexReversal_apply_apply (n : ℕ) (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    simplexReversal n (simplexReversal n x) = x := simplexReversal_involutive n x

@[simp]
theorem simplexReversal_comp_self (n : ℕ) :
    (simplexReversal n).comp (simplexReversal n) = ContinuousMap.id _ := by
  apply ContinuousMap.ext
  intro x
  exact simplexReversal_apply_apply n x

@[simp]
theorem simplexReversal_zero : simplexReversal 0 = ContinuousMap.id _ := by
  apply ContinuousMap.ext
  intro x
  exact Subsingleton.elim _ _

/-- The topological face that omits `i` is reversed to the face that omits `i.rev`. -/
theorem simplexReversal_face (n : ℕ) (i : Fin (n + 2)) :
    (simplexReversal (n + 1)).comp (Cohomology.Singular.ContinuousFormulas.standardSimplexFace i) =
      (Cohomology.Singular.ContinuousFormulas.standardSimplexFace i.rev).comp (simplexReversal n) := by
  apply ContinuousMap.ext
  intro x
  change Convexity.StdSimplex.map Fin.rev (Convexity.StdSimplex.map i.succAbove x) =
    Convexity.StdSimplex.map i.rev.succAbove (Convexity.StdSimplex.map Fin.rev x)
  rw [← Convexity.StdSimplex.map_comp, ← Convexity.StdSimplex.map_comp]
  congr 1
  funext j
  exact Fin.rev_succAbove i j

/-- Reverse an actual singular simplex by precomposing its continuous map. -/
def singularSimplexReversal (X : TopCat.{0}) (n : ℕ)
    (s : (TopCat.toSSet.obj X) _⦋n⦌) : (TopCat.toSSet.obj X) _⦋n⦌ :=
  (Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n).symm
    ((Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n s).comp (simplexReversal n))

@[simp]
theorem singularSimplexReversal_continuousMap (X : TopCat.{0}) (n : ℕ)
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n (singularSimplexReversal X n s) =
      (Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n s).comp (simplexReversal n) :=
  Equiv.apply_symm_apply _ _

theorem singularSimplexReversal_involutive (X : TopCat.{0}) (n : ℕ) :
    Function.Involutive (singularSimplexReversal X n) := by
  intro s
  apply (Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n).injective
  simp only [singularSimplexReversal_continuousMap]
  ext x
  simp

@[simp]
theorem singularSimplexReversal_apply_apply (X : TopCat.{0}) (n : ℕ)
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularSimplexReversal X n (singularSimplexReversal X n s) = s :=
  singularSimplexReversal_involutive X n s

@[simp]
theorem singularSimplexReversal_zero (X : TopCat.{0})
    (s : (TopCat.toSSet.obj X) _⦋0⦌) : singularSimplexReversal X 0 s = s := by
  apply (Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X 0).injective
  simp

/-- Reversing a singular simplex exchanges face `i` with face `i.rev`. -/
theorem singularSimplexReversal_face (X : TopCat.{0}) (n : ℕ)
    (i : Fin (n + 2)) (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    (TopCat.toSSet.obj X).δ i (singularSimplexReversal X (n + 1) s) =
      singularSimplexReversal X n ((TopCat.toSSet.obj X).δ i.rev s) := by
  apply (Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n).injective
  rw [Cohomology.Singular.ContinuousFormulas.singularSimplicesEquivContinuousMap_face, singularSimplexReversal_continuousMap,
    singularSimplexReversal_continuousMap, Cohomology.Singular.ContinuousFormulas.singularSimplicesEquivContinuousMap_face]
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, simplexReversal_face]

/-- Reversal commutes with every continuous map of target spaces. -/
theorem singularSimplexReversal_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularSimplexReversal Y n ((TopCat.toSSet.map f).app _ s) =
      (TopCat.toSSet.map f).app _ (singularSimplexReversal X n s) := by
  apply (Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap Y n).injective
  rw [singularSimplexReversal_continuousMap, Cohomology.Singular.ContinuousFormulas.singularSimplicesEquivContinuousMap_map,
    Cohomology.Singular.ContinuousFormulas.singularSimplicesEquivContinuousMap_map, singularSimplexReversal_continuousMap]
  exact ContinuousMap.comp_assoc _ _ _

/-- Reversal changes the parametrization, preserving the image of a singular simplex. -/
theorem singularSimplexReversal_range (X : TopCat.{0}) (n : ℕ)
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    Set.range (Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n (singularSimplexReversal X n s)) =
      Set.range (Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n s) := by
  rw [singularSimplexReversal_continuousMap]
  ext y
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨simplexReversal n x, hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨simplexReversal n x, ?_⟩
    simpa using hx

end

/-!
# Front and back restrictions under actual simplex reversal

Reversing the vertices sends a consecutive interval to the reversed
complementary-position interval. The identities are proved for the actual
continuous maps of standard simplices, and then for genuine singular
simplices. Reversal is not treated as a morphism in the simplex category.
-/

open _root_.CategoryTheory Opposite
open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Vertex reversal carries the interval starting at `a` to the reversed
interval starting at `n - a - p`. This is an equality of functions on vertices. -/
theorem finRev_subinterval {n : ℕ} (a p : ℕ) (h : a + p ≤ n)
    (i : Fin (p + 1)) :
    (((SimplexCategory.subinterval a p h).toOrderHom) i).rev =
      (SimplexCategory.subinterval (n - a - p) p (by omega)).toOrderHom i.rev := by
  apply Fin.ext
  change n + 1 - (i.val + a + 1) = (p + 1 - (i.val + 1)) + (n - a - p)
  omega

/-- Reversal and interval restriction agree as actual continuous maps
of topological standard simplices. -/
theorem simplexReversal_interval {n : ℕ} (a p : ℕ) (h : a + p ≤ n) :
    (simplexReversal n).comp (SimplexFaceIdentities.standardSimplexInterval a p h) =
      (SimplexFaceIdentities.standardSimplexInterval (n - a - p) p (by omega)).comp (simplexReversal p) := by
  apply ContinuousMap.ext
  intro z
  change Convexity.StdSimplex.map Fin.rev (Convexity.StdSimplex.map (SimplexCategory.subinterval a p h) z) =
    Convexity.StdSimplex.map (SimplexCategory.subinterval (n - a - p) p (by omega))
      (Convexity.StdSimplex.map Fin.rev z)
  rw [← Convexity.StdSimplex.map_comp, ← Convexity.StdSimplex.map_comp]
  apply congrArg (fun g : Fin (p + 1) → Fin (n + 1) => Convexity.StdSimplex.map g z)
  funext i
  exact finRev_subinterval a p h i

/-- The front block becomes the back block after reversal. Both sides
are continuous maps into the same actual `(p + q)`-simplex. -/
theorem simplexReversal_front (p q : ℕ) :
    (simplexReversal (p + q)).comp
        (SimplexFaceIdentities.standardSimplexInterval 0 p (show 0 + p ≤ p + q by omega)) =
      (SimplexFaceIdentities.standardSimplexInterval q p (show q + p ≤ p + q by omega)).comp
        (simplexReversal p) := by
  simpa only [Nat.sub_zero, Nat.add_sub_cancel_left] using
    simplexReversal_interval 0 p (show 0 + p ≤ p + q by omega)

/-- The back block becomes the front block after reversal, with the
common ambient simplex dimension retained explicitly. -/
theorem simplexReversal_back (p q : ℕ) :
    (simplexReversal (p + q)).comp (SimplexFaceIdentities.standardSimplexInterval p q le_rfl) =
      (SimplexFaceIdentities.standardSimplexInterval 0 q (show 0 + q ≤ p + q by omega)).comp
        (simplexReversal q) := by
  simpa only [Nat.add_sub_cancel_left, Nat.sub_self] using
    simplexReversal_interval p q (show p + q ≤ p + q from le_rfl)

/-- On genuine singular simplices, reversing before restricting to a
vertex interval equals restricting to the reversed interval and reversing. -/
theorem intervalFace_singularSimplexReversal (X : TopCat.{0}) {n : ℕ}
    (a p : ℕ) (h : a + p ≤ n) (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    SimplexFaceIdentities.intervalFace (TopCat.toSSet.obj X) a p h (singularSimplexReversal X n s) =
      singularSimplexReversal X p
        (SimplexFaceIdentities.intervalFace (TopCat.toSSet.obj X) (n - a - p) p (by omega) s) := by
  apply (X.toSSetObjEquiv (op ⦋p⦌)).injective
  have hrev (m : ℕ) (t : (TopCat.toSSet.obj X) _⦋m⦌) :
      X.toSSetObjEquiv (op ⦋m⦌) (singularSimplexReversal X m t) =
        (X.toSSetObjEquiv (op ⦋m⦌) t).comp (simplexReversal m) :=
    singularSimplexReversal_continuousMap X m t
  simp only [SimplexFaceIdentities.intervalFace_continuousMap, hrev,
    ContinuousMap.comp_assoc]
  rw [simplexReversal_interval]

/-- The front face of a reversed genuine singular simplex is the reversed
back face. The exchange of the two degree sums is an explicit transport. -/
theorem frontFace_singularSimplexReversal (X : TopCat.{0}) (p q : ℕ)
    (s : (TopCat.toSSet.obj X) _⦋p + q⦌) :
    SimplexFaceIdentities.frontFace (TopCat.toSSet.obj X) p q (singularSimplexReversal X (p + q) s) =
      singularSimplexReversal X p
        (SimplexFaceIdentities.backFace (TopCat.toSSet.obj X) q p
          (SimplexFaceIdentities.simplexCast (TopCat.toSSet.obj X) (Nat.add_comm p q) s)) := by
  unfold SimplexFaceIdentities.frontFace SimplexFaceIdentities.backFace
  rw [SimplexFaceIdentities.intervalFace_simplexCast]
  simpa only [Nat.sub_zero, Nat.add_sub_cancel_left] using
    intervalFace_singularSimplexReversal X 0 p (show 0 + p ≤ p + q by omega) s

/-- The back face of a reversed genuine singular simplex is the reversed
front face, again with the degree transport recorded explicitly. -/
theorem backFace_singularSimplexReversal (X : TopCat.{0}) (p q : ℕ)
    (s : (TopCat.toSSet.obj X) _⦋p + q⦌) :
    SimplexFaceIdentities.backFace (TopCat.toSSet.obj X) p q (singularSimplexReversal X (p + q) s) =
      singularSimplexReversal X q
        (SimplexFaceIdentities.frontFace (TopCat.toSSet.obj X) q p
          (SimplexFaceIdentities.simplexCast (TopCat.toSSet.obj X) (Nat.add_comm p q) s)) := by
  unfold SimplexFaceIdentities.frontFace SimplexFaceIdentities.backFace
  rw [SimplexFaceIdentities.intervalFace_simplexCast]
  simpa only [Nat.add_sub_cancel_left, Nat.sub_self] using
    intervalFace_singularSimplexReversal X p q (show p + q ≤ p + q from le_rfl) s

end

end OAI.AlgebraicTopology.Products.SimplexReversal
