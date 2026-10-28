import OAI.AlgebraicTopology.Kunneth.SimplexFormDomain
import OAI.AlgebraicTopology.Kunneth.RestrictedFormPullback

/-! # Simplex Form Maps -/

namespace OAI.AlgebraicTopology.Kunneth.SimplexFormMaps

noncomputable section

/-! Affine simplex operators and their contravariant action on restricted forms. -/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false

open Set
open scoped BigOperators ContDiff

namespace Constructions

theorem simplexBarycentric_recover (n : ℕ) (y : Fin (n + 1) → ℝ) (hy : ∑ i, y i = 1) :
    SimplexFormDomain.Constructions.simplexBarycentric n (fun i => y i.castSucc) = y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [SimplexFormDomain.Constructions.simplexBarycentric_last]
    rw [Fin.sum_univ_castSucc] at hy
    linarith
  · exact SimplexFormDomain.Constructions.simplexBarycentric_castSucc n _ j

theorem coordinateSimplex_of_barycentric {n : ℕ} {y : Fin (n + 1) → ℝ}
    (hy : y ∈ Set.range (fun x : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
      (x.weights : Fin (n + 1) → ℝ))) :
    (fun i : Fin n => y i.castSucc) ∈ SimplexFormDomain.Constructions.coordinateSimplex n := by
  rcases hy with ⟨y, rfl⟩
  refine ⟨fun i => y.weights_nonneg i.castSucc, ?_⟩
  have hsum := y.total_of_fintype
  rw [Fin.sum_univ_castSucc] at hsum
  have hlast := y.weights_nonneg (Fin.last n)
  linarith

theorem simplexLinearMap_sum {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (x : Fin (m + 1) → ℝ) :
    ∑ j, Cohomology.Singular.Smooth.simplexLinearMap f x j = ∑ i, x i := by
  change ∑ j, FunOnFinite.linearMap ℝ ℝ f x j = _
  simp only [FunOnFinite.linearMap_apply_apply]
  exact Finset.sum_fiberwise Finset.univ f x

def simplexCoordinateMap {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (x : Fin m → ℝ) : Fin n → ℝ :=
  fun j => Cohomology.Singular.Smooth.simplexLinearMap f (SimplexFormDomain.Constructions.simplexBarycentric m x) j.castSucc

theorem simplexCoordinateMap_contDiff {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    ContDiff ℝ ∞ (simplexCoordinateMap f) := by
  apply contDiff_pi.mpr
  intro j
  exact (contDiff_apply ℝ ℝ j.castSucc).comp
    ((Cohomology.Singular.Smooth.simplexLinearMap f).contDiff.comp (SimplexFormDomain.Constructions.simplexBarycentric_contDiff m))

theorem simplexCoordinateMap_barycentric {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (x : Fin m → ℝ) :
    SimplexFormDomain.Constructions.simplexBarycentric n (simplexCoordinateMap f x) =
      Cohomology.Singular.Smooth.simplexLinearMap f (SimplexFormDomain.Constructions.simplexBarycentric m x) :=
  simplexBarycentric_recover n _ ((simplexLinearMap_sum f _).trans (SimplexFormDomain.Constructions.simplexBarycentric_sum m x))

theorem simplexCoordinateMap_mapsTo {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    MapsTo (simplexCoordinateMap f) (SimplexFormDomain.Constructions.coordinateSimplex m) (SimplexFormDomain.Constructions.coordinateSimplex n) := by
  intro x hx
  apply coordinateSimplex_of_barycentric
  refine ⟨Convexity.StdSimplex.map f (SimplexFormDomain.Constructions.simplexBarycentricPoint x hx), ?_⟩
  change (Convexity.StdSimplex.map f (SimplexFormDomain.Constructions.simplexBarycentricPoint x hx) : Fin (n + 1) → ℝ) =
    Cohomology.Singular.Smooth.simplexLinearMap f (SimplexFormDomain.Constructions.simplexBarycentric m x)
  rw [← Cohomology.Singular.Smooth.simplexLinearMap_weights, SimplexFormDomain.Constructions.simplexBarycentricPoint_weights]

theorem simplexCoordinateMap_id (n : ℕ) :
    simplexCoordinateMap (id : Fin (n + 1) → Fin (n + 1)) = id := by
  funext x j
  change FunOnFinite.linearMap ℝ ℝ id (SimplexFormDomain.Constructions.simplexBarycentric n x) j.castSucc = x j
  rw [FunOnFinite.linearMap_id]
  exact SimplexFormDomain.Constructions.simplexBarycentric_castSucc n x j

theorem simplexCoordinateMap_comp {l m n : ℕ}
    (f : Fin (l + 1) → Fin (m + 1)) (g : Fin (m + 1) → Fin (n + 1)) :
    simplexCoordinateMap (g ∘ f) = simplexCoordinateMap g ∘ simplexCoordinateMap f := by
  funext x j
  change Cohomology.Singular.Smooth.simplexLinearMap (g ∘ f) (SimplexFormDomain.Constructions.simplexBarycentric l x) j.castSucc =
    Cohomology.Singular.Smooth.simplexLinearMap g (SimplexFormDomain.Constructions.simplexBarycentric m (simplexCoordinateMap f x)) j.castSucc
  rw [simplexCoordinateMap_barycentric]
  change FunOnFinite.linearMap ℝ ℝ (g ∘ f) (SimplexFormDomain.Constructions.simplexBarycentric l x) j.castSucc =
    FunOnFinite.linearMap ℝ ℝ g (FunOnFinite.linearMap ℝ ℝ f (SimplexFormDomain.Constructions.simplexBarycentric l x)) j.castSucc
  rw [FunOnFinite.linearMap_comp]
  rfl

def simplexFormPullback {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (k : ℕ) :
    RestrictedForms.Constructions.RestrictedForm (SimplexFormDomain.Constructions.coordinateSimplex n) k →ₗ[ℂ] RestrictedForms.Constructions.RestrictedForm (SimplexFormDomain.Constructions.coordinateSimplex m) k :=
  RestrictedFormPullback.Constructions.restrictedFormPullback (simplexCoordinateMap f) (simplexCoordinateMap_contDiff f)
    (simplexCoordinateMap_mapsTo f) k

theorem simplexFormPullback_d {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (k : ℕ)
    (a : RestrictedForms.Constructions.RestrictedForm (SimplexFormDomain.Constructions.coordinateSimplex n) k) :
    RestrictedForms.Constructions.restrictedFormD (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn m) k (simplexFormPullback f k a) =
      simplexFormPullback f (k + 1) (RestrictedForms.Constructions.restrictedFormD (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n) k a) :=
  RestrictedFormPullback.Constructions.restrictedFormPullback_d (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn m) (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n)
    (simplexCoordinateMap f) (simplexCoordinateMap_contDiff f) (simplexCoordinateMap_mapsTo f) k a

theorem simplexFormPullback_id (n k : ℕ) (a : RestrictedForms.Constructions.RestrictedForm (SimplexFormDomain.Constructions.coordinateSimplex n) k) :
    simplexFormPullback (id : Fin (n + 1) → Fin (n + 1)) k a = a := by
  dsimp only [simplexFormPullback]
  calc
    _ = RestrictedFormPullback.Constructions.restrictedFormPullback id contDiff_id (mapsTo_id (SimplexFormDomain.Constructions.coordinateSimplex n)) k a :=
      RestrictedFormPullback.Constructions.restrictedFormPullback_congr (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n) _ id _ _ _ _
        (fun x _ => congrFun (simplexCoordinateMap_id n) x) k a
    _ = a := RestrictedFormPullback.Constructions.restrictedFormPullback_id _ _ a

theorem simplexFormPullback_comp {l m n : ℕ}
    (f : Fin (l + 1) → Fin (m + 1)) (g : Fin (m + 1) → Fin (n + 1))
    (k : ℕ) (a : RestrictedForms.Constructions.RestrictedForm (SimplexFormDomain.Constructions.coordinateSimplex n) k) :
    simplexFormPullback (g ∘ f) k a = simplexFormPullback f k (simplexFormPullback g k a) := by
  dsimp only [simplexFormPullback]
  calc
    _ = RestrictedFormPullback.Constructions.restrictedFormPullback (simplexCoordinateMap g ∘ simplexCoordinateMap f)
        ((simplexCoordinateMap_contDiff g).comp (simplexCoordinateMap_contDiff f))
        ((simplexCoordinateMap_mapsTo g).comp (simplexCoordinateMap_mapsTo f)) k a :=
      RestrictedFormPullback.Constructions.restrictedFormPullback_congr (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn l) _ _ _ _ _ _
        (fun x _ => congrFun (simplexCoordinateMap_comp f g) x) k a
    _ = _ := RestrictedFormPullback.Constructions.restrictedFormPullback_comp _ _ _ _ _ _ k a

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.SimplexFormMaps
