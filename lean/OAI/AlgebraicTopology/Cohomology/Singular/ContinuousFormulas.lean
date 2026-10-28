import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicTopology.Cohomology.Singular.Formulas
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-! # Continuous Formulas -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas

noncomputable section

/-!
# Singular cochain formulas on continuous maps from standard simplices

This file expresses the previously proved simplicial formulas in the actual
function module `C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) → M`. The coefficient-valued
functions are arbitrary; continuity is required of the singular simplices.
The faces are the usual inclusions omitting one barycentric coordinate.
-/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

open _root_.CategoryTheory Opposite
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The standard simplex face that omits barycentric coordinate `i`. -/
def standardSimplexFace {n : ℕ} (i : Fin (n + 2)) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), Convexity.StdSimplex ℝ (Fin (n + 2))) :=
  ⟨Convexity.StdSimplex.map i.succAbove, Convexity.StdSimplex.continuous_map ℝ i.succAbove⟩

/-- The face map is the actual map of topological standard simplices. -/
theorem standardSimplexFace_apply {n : ℕ} (i : Fin (n + 2))
    (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    standardSimplexFace i z = Convexity.StdSimplex.map i.succAbove z := rfl

/-- A face in the singular simplicial set is precomposition with its face inclusion. -/
theorem singularSimplicesEquivContinuousMap_face (X : TopCat.{0}) {n : ℕ}
    (s : Basic.singularSimplices X (n + 1)) (i : Fin (n + 2)) :
    Coefficients.singularSimplicesEquivContinuousMap X n ((TopCat.toSSet.obj X).δ i s) =
      (Coefficients.singularSimplicesEquivContinuousMap X (n + 1) s).comp (standardSimplexFace i) := by
  ext z
  exact TopCat.toSSetObjEquiv_δ_apply s i z

/-- The continuous-map-to-simplex identification also respects each face inclusion. -/
theorem singularSimplicesEquivContinuousMap_symm_face (X : TopCat.{0}) {n : ℕ}
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 2)), X)) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj X).δ i ((Coefficients.singularSimplicesEquivContinuousMap X (n + 1)).symm s) =
      (Coefficients.singularSimplicesEquivContinuousMap X n).symm (s.comp (standardSimplexFace i)) := by
  apply (Coefficients.singularSimplicesEquivContinuousMap X n).injective
  rw [singularSimplicesEquivContinuousMap_face, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

/-- A continuous map of spaces acts on singular simplices by postcomposition. -/
theorem singularSimplicesEquivContinuousMap_map {X Y : TopCat.{0}}
    (f : X ⟶ Y) {n : ℕ} (s : Basic.singularSimplices X n) :
    Coefficients.singularSimplicesEquivContinuousMap Y n ((TopCat.toSSet.map f).app _ s) =
      f.hom.comp (Coefficients.singularSimplicesEquivContinuousMap X n s) := rfl

/-- Postcomposition agrees with the singular simplicial map under the inverse identification. -/
theorem singularSimplicesEquivContinuousMap_symm_map {X Y : TopCat.{0}}
    (f : X ⟶ Y) {n : ℕ} (s : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
    (TopCat.toSSet.map f).app _ ((Coefficients.singularSimplicesEquivContinuousMap X n).symm s) =
      (Coefficients.singularSimplicesEquivContinuousMap Y n).symm (f.hom.comp s) := by
  apply (Coefficients.singularSimplicesEquivContinuousMap Y n).injective
  rw [singularSimplicesEquivContinuousMap_map, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

variable {R : Type} [Ring R]

/-- The continuous-simplex function isomorphism evaluates through the inverse simplex equivalence. -/
theorem singularDegreewiseContinuousFunctionIso_hom_apply (M : ModuleCat.{0} R)
    (X : TopCat.{0}) {n : ℕ} (c : (Basic.singularCochains M X).X n)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
    (Coefficients.singularDegreewiseContinuousFunctionIso M X n).hom c s =
      (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M n).hom c
        ((Coefficients.singularSimplicesEquivContinuousMap X n).symm s) := rfl

/-- In functions on genuine continuous singular simplices, the differential is the usual
alternating sum of restrictions to the topological simplex faces. -/
theorem singularDegreewiseContinuousFunctionIso_coboundary (M : ModuleCat.{0} R)
    (X : TopCat.{0}) {n : ℕ} (c : (Basic.singularCochains M X).X n)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 2)), X)) :
    (Coefficients.singularDegreewiseContinuousFunctionIso M X (n + 1)).hom
        ((Basic.singularCochains M X).d n (n + 1) c) s =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
        (Coefficients.singularDegreewiseContinuousFunctionIso M X n).hom c
          (s.comp (standardSimplexFace i)) := by
  calc
    _ = (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M (n + 1)).hom
        ((Basic.singularCochains M X).d n (n + 1) c)
        ((Coefficients.singularSimplicesEquivContinuousMap X (n + 1)).symm s) :=
      singularDegreewiseContinuousFunctionIso_hom_apply M X _ s
    _ = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
        (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M n).hom c
          ((TopCat.toSSet.obj X).δ i
            ((Coefficients.singularSimplicesEquivContinuousMap X (n + 1)).symm s)) :=
      Formulas.degreewiseFunctionIso_coboundary (TopCat.toSSet.obj X) M c _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [singularSimplicesEquivContinuousMap_symm_face]
      exact congrArg (fun v : M => ((-1 : ℤ) ^ i.val) • v)
        (singularDegreewiseContinuousFunctionIso_hom_apply M X c
          (s.comp (standardSimplexFace i))).symm

/-- In functions on genuine continuous singular simplices, cochain pullback is
precomposition with postcomposition of simplices by the continuous map of spaces. -/
theorem singularDegreewiseContinuousFunctionIso_pullback (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {n : ℕ} (c : (Basic.singularCochains M Y).X n)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
    (Coefficients.singularDegreewiseContinuousFunctionIso M X n).hom ((Functor.singularPullback M f).f n c) s =
      (Coefficients.singularDegreewiseContinuousFunctionIso M Y n).hom c (f.hom.comp s) := by
  calc
    _ = (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M n).hom
        ((Functor.singularPullback M f).f n c) ((Coefficients.singularSimplicesEquivContinuousMap X n).symm s) :=
      singularDegreewiseContinuousFunctionIso_hom_apply M X _ s
    _ = (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj Y) M n).hom c
        ((TopCat.toSSet.map f).app _ ((Coefficients.singularSimplicesEquivContinuousMap X n).symm s)) :=
      Formulas.degreewiseFunctionIso_pullback M (TopCat.toSSet.map f) c _
    _ = _ := by
      rw [singularSimplicesEquivContinuousMap_symm_map]
      exact (singularDegreewiseContinuousFunctionIso_hom_apply M Y c (f.hom.comp s)).symm

/-- Every function on continuous singular simplices defines a cochain, and its
coboundary is the alternating face sum. No support or regularity restriction is imposed on `φ`. -/
theorem continuousFunction_coboundary (M : ModuleCat.{0} R) (X : TopCat.{0}) {n : ℕ}
    (φ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) → M)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 2)), X)) :
    (Coefficients.singularDegreewiseContinuousFunctionIso M X (n + 1)).hom
        ((Basic.singularCochains M X).d n (n + 1)
          ((Coefficients.singularDegreewiseContinuousFunctionIso M X n).inv φ)) s =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) • φ (s.comp (standardSimplexFace i)) := by
  calc
    _ = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
        (Coefficients.singularDegreewiseContinuousFunctionIso M X n).hom
          ((Coefficients.singularDegreewiseContinuousFunctionIso M X n).inv φ)
          (s.comp (standardSimplexFace i)) :=
      singularDegreewiseContinuousFunctionIso_coboundary M X _ s
    _ = _ := congrArg
      (fun ψ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) → M =>
        ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) • ψ (s.comp (standardSimplexFace i)))
      (ModuleCat.hom_inv_apply (Coefficients.singularDegreewiseContinuousFunctionIso M X n) φ)

/-- Pullback of the cochain defined by any function on continuous singular simplices
is precomposition by postcomposition of the simplices. -/
theorem continuousFunction_pullback (M : ModuleCat.{0} R) {X Y : TopCat.{0}}
    (f : X ⟶ Y) {n : ℕ} (φ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), Y) → M)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
    (Coefficients.singularDegreewiseContinuousFunctionIso M X n).hom
        ((Functor.singularPullback M f).f n
          ((Coefficients.singularDegreewiseContinuousFunctionIso M Y n).inv φ)) s =
      φ (f.hom.comp s) := by
  calc
    _ = (Coefficients.singularDegreewiseContinuousFunctionIso M Y n).hom
        ((Coefficients.singularDegreewiseContinuousFunctionIso M Y n).inv φ) (f.hom.comp s) :=
      singularDegreewiseContinuousFunctionIso_pullback M f _ s
    _ = _ := congrFun
      (ModuleCat.hom_inv_apply (Coefficients.singularDegreewiseContinuousFunctionIso M Y n) φ) _

end

end OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas
