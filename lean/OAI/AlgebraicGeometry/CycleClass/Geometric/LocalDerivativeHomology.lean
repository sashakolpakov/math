import OAI.AlgebraicGeometry.CycleClass.Geometric.DerivativePuncturedHomotopy
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomotopy
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalExcision
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLinearPuncturedHomotopy
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Local Derivative Homology -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocalDerivativeHomology.Cycles

noncomputable section

/-!
# Local homology of a differentiable coordinate change

The actual homotopy from a map to its derivative is a homotopy of punctured
pairs on a small ball. Relative homotopy invariance and proved local excision
therefore identify its induced local homology map with that of its derivative.
For a complex-linear invertible derivative this map preserves the entire
orientation-degree local homology group. No orientation generator is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicTopology
open scoped _root_.Topology

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A real invertible linear map as an actual continuous map of spaces. -/
def linearNormalMap (L : E ≃L[ℝ] F) : TopCat.of E ⟶ TopCat.of F :=
  TopCat.ofHom ⟨L, L.continuous⟩

theorem linearNormalMap_preservesPuncture (L : E ≃L[ℝ] F) :
    Set.MapsTo (linearNormalMap L) ({0}ᶜ : Set E) ({0}ᶜ : Set F) := by
  intro x hx
  change L x ≠ 0
  intro he
  exact hx (L.injective (by simpa only [map_zero] using he))

/-- The actual local homology map of an invertible real linear map. -/
def linearLocalHomologyMap (L : E ≃L[ℝ] F) (n : ℕ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of E) 0 n ⟶
      LocalHomology.Cycles.localSingularHomology (TopCat.of F) 0 n :=
  LocalHomology.Cycles.relativeSingularHomologyMap (linearNormalMap L)
    (linearNormalMap_preservesPuncture L) n

/-- The distinguished point of a positive-radius coordinate ball. -/
abbrev ballZero (E : Type) [NormedAddCommGroup E] (r : ℝ) (hr : 0 < r) :
    Metric.ball (0 : E) r := ⟨0, by simpa using hr⟩

def linearBallMap (L : E ≃L[ℝ] F) (r : ℝ) :
    TopCat.of (Metric.ball (0 : E) r) ⟶ TopCat.of F :=
  TopCat.ofHom ⟨fun x => L x.1, L.continuous.comp continuous_subtype_val⟩

def translatedBallMap (f : E → F) (r : ℝ)
    (hc : ContinuousOn f (Metric.ball 0 r)) :
    TopCat.of (Metric.ball (0 : E) r) ⟶ TopCat.of F :=
  TopCat.ofHom ⟨fun x => f x.1 - f 0,
    (hc.domRestrict).sub continuous_const⟩

/-- The straight line on the full coordinate ball, including its center. -/
def derivativeBallHomotopy (f : E → F) (L : E ≃L[ℝ] F) (r : ℝ)
    (hc : ContinuousOn f (Metric.ball 0 r)) :
    TopCat.Homotopy (linearBallMap L r) (translatedBallMap f r hc) where
  toFun z := L z.2.1 + (z.1 : ℝ) • (f z.2.1 - f 0 - L z.2.1)
  continuous_toFun :=
    (L.continuous.comp (continuous_subtype_val.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (((hc.domRestrict.comp continuous_snd).sub continuous_const).sub
          (L.continuous.comp (continuous_subtype_val.comp continuous_snd))))
  map_zero_left x := by simp [linearBallMap]
  map_one_left x := by
    change L x.1 + (1 : ℝ) • (f x.1 - f 0 - L x.1) = f x.1 - f 0
    simp

theorem derivativeBallHomotopy_preservesPuncture (f : E → F)
    (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r)
    (hc : ContinuousOn f (Metric.ball 0 r))
    (he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖) :
    ∀ t : unitInterval, Set.MapsTo
      (fun x => derivativeBallHomotopy f L r hc (t, x))
      ({ballZero E r hr}ᶜ : Set (Metric.ball (0 : E) r)) ({0}ᶜ : Set F) := by
  intro t x hx
  change x ≠ ballZero E r hr at hx
  change L x.1 + (t : ℝ) • ((f x.1 - f 0) - L x.1) ≠ 0
  apply DerivativePuncturedHomotopy.Cycles.straightLine_ne_zero_of_half_norm
  · intro hL
    apply hx
    apply Subtype.ext
    change x.1 = 0
    exact L.injective (by simpa only [map_zero] using hL)
  · apply he
    simpa only [Metric.mem_ball, dist_zero_right] using x.property

theorem linearBallMap_preservesPuncture (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r) :
    Set.MapsTo (linearBallMap L r)
      ({ballZero E r hr}ᶜ : Set (Metric.ball (0 : E) r)) ({0}ᶜ : Set F) := by
  intro x hx
  change x ≠ ballZero E r hr at hx
  change L x.1 ≠ 0
  intro hL
  exact hx (Subtype.ext (L.injective (by simpa only [map_zero] using hL)))

theorem translatedBallMap_preservesPuncture (f : E → F)
    (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r)
    (hc : ContinuousOn f (Metric.ball 0 r))
    (he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖) :
    Set.MapsTo (translatedBallMap f r hc)
      ({ballZero E r hr}ᶜ : Set (Metric.ball (0 : E) r)) ({0}ᶜ : Set F) :=
  RelativeHomotopy.Cycles.homotopy_end_mapsTo (derivativeBallHomotopy f L r hc)
    (derivativeBallHomotopy_preservesPuncture f L r hr hc he)

def translatedBallLocalHomologyMap (f : E → F)
    (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r)
    (hc : ContinuousOn f (Metric.ball 0 r))
    (he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖) (n : ℕ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (Metric.ball (0 : E) r)) (ballZero E r hr) n ⟶
      LocalHomology.Cycles.localSingularHomology (TopCat.of F) 0 n :=
  LocalHomology.Cycles.relativeSingularHomologyMap (translatedBallMap f r hc)
    (translatedBallMap_preservesPuncture f L r hr hc he) n

/-- The nonlinear map and derivative induce equal relative homology maps
on the ball because the explicit homotopy preserves the punctured pair. -/
theorem translatedBallLocalHomologyMap_eq_linear (f : E → F)
    (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r)
    (hc : ContinuousOn f (Metric.ball 0 r))
    (he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖) (n : ℕ) :
    translatedBallLocalHomologyMap f L r hr hc he n =
      LocalHomology.Cycles.relativeSingularHomologyMap (linearBallMap L r)
        (linearBallMap_preservesPuncture L r hr) n :=
  (RelativeHomotopy.Cycles.relativeSingularHomologyMap_eq_of_homotopy
    (linearBallMap_preservesPuncture L r hr)
    (translatedBallMap_preservesPuncture f L r hr hc he)
    (derivativeBallHomotopy f L r hc)
    (derivativeBallHomotopy_preservesPuncture f L r hr hc he) n).symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual linear map of punctured pairs factors through neighborhood
inclusion, before passing to homology. -/
theorem linearBallRelativeMap_factor (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r) :
    LocalExcision.Cycles.localExcisionChainMap (TopCat.of E) (Metric.ball 0 r) 0
        (by simpa using hr) ≫
      LocalHomology.Cycles.relativeSingularChainsMap (linearNormalMap L) (linearNormalMap_preservesPuncture L) =
    LocalHomology.Cycles.relativeSingularChainsMap (linearBallMap L r) (linearBallMap_preservesPuncture L r hr) := by
  unfold LocalExcision.Cycles.localExcisionChainMap
  rw [LocalHomology.Cycles.relativeSingularChainsMap_comp]
  rfl

/-- Excision identifies the local action of a differentiable germ with the
local action of its derivative. -/
theorem translatedBallLocalHomologyMap_eq_excision_comp (f : E → F)
    (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r)
    (hc : ContinuousOn f (Metric.ball 0 r))
    (he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖) (n : ℕ) :
    translatedBallLocalHomologyMap f L r hr hc he n =
      (LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of E) (Metric.ball 0 r) 0
        (by simpa using hr) Metric.isOpen_ball n).hom ≫ linearLocalHomologyMap L n := by
  rw [translatedBallLocalHomologyMap_eq_linear, LocalExcision.Cycles.localExcisionHomologyIso_hom]
  change HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp, linearBallRelativeMap_factor]

/-- Complex-linear invertible derivatives preserve every local homology
class above degree one, without choosing a generator. -/
theorem complexLinearLocalHomologyMap_eq_id {p : ℕ}
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ)) (n : ℕ) (hn : 1 < n) :
    linearLocalHomologyMap (L.restrictScalars ℝ) n = 𝟙 _ := by
  let A := LinearMap.toMatrix' L.toLinearEquiv.toLinearMap
  have hA : IsUnit A :=
    LinearMap.isUnit_toMatrix'_iff.mpr ((Module.End.isUnit_iff _).mpr L.bijective)
  have hm : linearNormalMap (L.restrictScalars ℝ) = TopCat.ofHom (ComplexLinearPuncturedHomotopy.Cycles.complexMatrixMap A) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact (LinearMap.toMatrix'_mulVec L.toLinearEquiv.toLinearMap x).symm
  simpa only [linearLocalHomologyMap, hm, ComplexLinearPuncturedHomotopy.Cycles.complexMatrixLocalHomologyMap] using
    ComplexLinearPuncturedHomotopy.Cycles.complexMatrixLocalHomologyMap_eq_id A hA n hn

set_option backward.isDefEq.respectTransparency false in
/-- A nonlinear map with invertible complex derivative preserves the actual
orientation-degree local homology, on a sufficiently small ball. -/
theorem exists_complexDerivative_localHomology_eq_excision {p : ℕ} (hp : 0 < p)
    (f : (Fin p → ℂ) → (Fin p → ℂ))
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ))
    (hf : HasFDerivAt f ((L.restrictScalars ℝ) : _ →L[ℝ] _) 0)
    {U : Set (Fin p → ℂ)} (hU : U ∈ 𝓝 (0 : Fin p → ℂ)) (hc : ContinuousOn f U) :
    ∃ (r : ℝ) (hr : 0 < r) (hc' : ContinuousOn f (Metric.ball 0 r))
      (he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖),
      Metric.ball (0 : Fin p → ℂ) r ⊆ U ∧
      translatedBallLocalHomologyMap f (L.restrictScalars ℝ) r hr hc' he (2 * p) =
        (LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of (Fin p → ℂ)) (Metric.ball 0 r) 0
          (by simpa using hr) Metric.isOpen_ball (2 * p)).hom := by
  have hmem : U ∩ {x | ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖} ∈
      𝓝 (0 : Fin p → ℂ) :=
    Filter.inter_mem hU (DerivativePuncturedHomotopy.Cycles.eventually_derivative_remainder_small (L.restrictScalars ℝ) hf)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hmem
  have hsub : Metric.ball (0 : Fin p → ℂ) r ⊆ U := fun _ hx => (hball hx).1
  have hc' : ContinuousOn f (Metric.ball 0 r) := hc.mono hsub
  have he : ∀ x, ‖x‖ < r → ‖f x - f 0 - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖ := by
    intro x hx
    exact (hball (by simpa only [Metric.mem_ball, dist_zero_right] using hx)).2
  refine ⟨r, hr, hc', he, hsub, ?_⟩
  rw [translatedBallLocalHomologyMap_eq_excision_comp,
    complexLinearLocalHomologyMap_eq_id L (2 * p) (by omega), Category.comp_id]

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocalDerivativeHomology.Cycles
