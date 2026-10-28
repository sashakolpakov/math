import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SchemeHolomorphic
import OAI.AlgebraicGeometry.Hodge.AnalyticDifferentialForms

/-! # Holomorphic Pullback -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HolomorphicPullback

noncomputable section

/-! # Actual pullback of the original holomorphic functions and Kähler forms

The source is the actual analytic preimage open. The algebra map is
precomposition with the genuine scheme-point map; exterior differentiation
commutes with the induced map on the original Kähler forms.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

variable {X Y : Over (Spec (.of ℂ))}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

/-- The genuine analytic preimage of an open under the original scheme-point map. -/
def originalAnalyticPreimage (f : X ⟶ Y) (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) :
    Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) :=
  ⟨ComplexPoint.Basic.Point.map f ⁻¹' (U : Set (ComplexPoint.Basic.ComplexSchemePoint Y)),
    U.isOpen.preimage (ComplexPoint.Basic.Point.continuousMap f).continuous⟩

/-- Restriction of the actual holomorphic scheme-point map to its actual preimage open. -/
def originalHolomorphicOpenMap (f : X ⟶ Y)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) :
    C^ω⟮𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ), originalAnalyticPreimage f U;
      𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) → ℂ), U⟯ := by
  refine ⟨fun x => ⟨ComplexPoint.Basic.Point.map f x.val, x.property⟩, ?_⟩
  intro x
  apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
    (P := ContDiffWithinAtProp 𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
      𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) → ℂ) ω) _ Set.univ x).mp
  exact ((SchemeHolomorphic.contMDiff_schemeMap_original f).comp contMDiff_subtype_val) x

/-- Actual pullback of original holomorphic functions, bundled as a complex algebra map. -/
def originalHolomorphicFunctionPullback (f : X ⟶ Y)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) :
    ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U) →ₐ[ℂ]
      ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op (originalAnalyticPreimage f U)) where
  toFun g := ContMDiffMap.comp g (originalHolomorphicOpenMap f U)
  map_one' := ContMDiffMap.ext fun _ => rfl
  map_mul' _ _ := ContMDiffMap.ext fun _ => rfl
  map_zero' := ContMDiffMap.ext fun _ => rfl
  map_add' _ _ := ContMDiffMap.ext fun _ => rfl
  commutes' _ := ContMDiffMap.ext fun _ => rfl

@[simp]
theorem originalHolomorphicFunctionPullback_apply (f : X ⟶ Y)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
    (g : ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U))
    (x : originalAnalyticPreimage f U) :
    (originalHolomorphicFunctionPullback f U g).1 x =
      g.1 ⟨ComplexPoint.Basic.Point.map f x.val, x.property⟩ := rfl

/-- Pullback of the original Kähler forms before passage to their chart-evaluation quotient. -/
def originalKahlerFormPullback (f : X ⟶ Y)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) (p : ℕ) :
    Algebra.DeRham.Basic.Form ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U)) p →ₗ[ℂ]
      Algebra.DeRham.Basic.Form ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X (Topology.Dimension.Basic.TopologicalSpace.dim X.left)
        (Opposite.op (originalAnalyticPreimage f U))) p :=
  Algebra.DeRham.Basic.map ℂ (originalHolomorphicFunctionPullback f U) p

/-- Exterior differentiation commutes with actual holomorphic Kähler-form pullback. -/
theorem originalKahlerFormPullback_differential (f : X ⟶ Y)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) (p : ℕ)
    (a : Algebra.DeRham.Basic.Form ℂ
      (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U)) p) :
    originalKahlerFormPullback f U (p + 1)
        (Algebra.DeRham.Basic.differential ℂ
          (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) (Opposite.op U)) p a) =
      Algebra.DeRham.Basic.differential ℂ
        (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X (Topology.Dimension.Basic.TopologicalSpace.dim X.left)
          (Opposite.op (originalAnalyticPreimage f U))) p
        (originalKahlerFormPullback f U p a) :=
  Algebra.DeRham.BasicSquared.map_differential ℂ (originalHolomorphicFunctionPullback f U) p a

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HolomorphicPullback
