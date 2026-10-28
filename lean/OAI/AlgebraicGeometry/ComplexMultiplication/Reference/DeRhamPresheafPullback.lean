import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HolomorphicFormPullback
import OAI.AlgebraicGeometry.Hodge.HolomorphicDeRham
import Mathlib.Topology.Sheaves.Functors

/-! # De Rham Presheaf Pullback -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DeRhamPresheafPullback

noncomputable section

/-! # Actual pullback on the original holomorphic de Rham presheaves

Function and form pullback commute with restriction to smaller opens. These
maps assemble into a morphism of the original presheaf de Rham complexes.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

variable {X Y : Over (Spec (.of ℂ))}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

/-- The actual continuous scheme-point map with the original analytic topologies. -/
def originalAnalyticSchemeMap (f : X ⟶ Y) :
    TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X) ⟶ TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y) :=
  TopCat.ofHom (ComplexPoint.Basic.Point.continuousMap f)

instance originalPresheafPushforward_preservesZeroMorphisms (f : X ⟶ Y) :
    (TopCat.Presheaf.pushforward AddCommGrpCat
      (originalAnalyticSchemeMap f)).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- The map of actual preimage opens, in the variance used for restriction. -/
def originalAnalyticPreimageRestriction (f : X ⟶ Y)
    {U V : (Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))ᵒᵖ} (i : U ⟶ V) :
    Opposite.op (HolomorphicPullback.originalAnalyticPreimage f U.unop) ⟶
      Opposite.op (HolomorphicPullback.originalAnalyticPreimage f V.unop) :=
  ((Opens.map (originalAnalyticSchemeMap f)).op).map i

/-- Pullback of genuine holomorphic functions commutes with actual restriction. -/
theorem originalHolomorphicFunctionPullback_restriction (f : X ⟶ Y)
    {U V : (Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))ᵒᵖ} (i : U ⟶ V) :
    (HolomorphicPullback.originalHolomorphicFunctionPullback f V.unop).comp
        (ComplexPoint.Basic.ComplexSchemePoint.holomorphicRestrictionAlgHom Y (OAI.Topology.Dimension.Basic.TopologicalSpace.dim Y.left) i) =
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicRestrictionAlgHom X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left)
        (originalAnalyticPreimageRestriction f i)).comp
          (HolomorphicPullback.originalHolomorphicFunctionPullback f U.unop) := by
  apply AlgHom.ext
  intro g
  exact ContMDiffMap.ext fun _ => rfl

/-- Pullback of the original Kähler forms commutes with actual restriction. -/
theorem originalKahlerFormPullback_restriction (f : X ⟶ Y)
    {U V : (Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))ᵒᵖ} (i : U ⟶ V) (p : ℕ) :
    (HolomorphicPullback.originalKahlerFormPullback f V.unop p).comp (ComplexPoint.Basic.ComplexSchemePoint.formRestriction Y (OAI.Topology.Dimension.Basic.TopologicalSpace.dim Y.left) i p) =
      (ComplexPoint.Basic.ComplexSchemePoint.formRestriction X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) (originalAnalyticPreimageRestriction f i) p).comp
        (HolomorphicPullback.originalKahlerFormPullback f U.unop p) := by
  unfold HolomorphicPullback.originalKahlerFormPullback ComplexPoint.Basic.ComplexSchemePoint.formRestriction
  rw [← Algebra.DeRham.Basic.map_comp, ← Algebra.DeRham.Basic.map_comp,
    originalHolomorphicFunctionPullback_restriction]

/-- Pullback on the unchanged form quotient commutes with actual restriction. -/
theorem originalHolomorphicFormPullback_restriction (f : X ⟶ Y)
    {U V : (Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))ᵒᵖ} (i : U ⟶ V) (p : ℕ) :
    (HolomorphicFormPullback.originalHolomorphicFormPullback f V.unop p).comp
        (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction Y (OAI.Topology.Dimension.Basic.TopologicalSpace.dim Y.left) i p) =
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left)
        (originalAnalyticPreimageRestriction f i) p).comp
          (HolomorphicFormPullback.originalHolomorphicFormPullback f U.unop p) := by
  apply LinearMap.ext
  intro θ
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel Y (OAI.Topology.Dimension.Basic.TopologicalSpace.dim Y.left) U p) θ
  change Submodule.Quotient.mk
    (HolomorphicPullback.originalKahlerFormPullback f V.unop p (ComplexPoint.Basic.ComplexSchemePoint.formRestriction Y (OAI.Topology.Dimension.Basic.TopologicalSpace.dim Y.left) i p a)) =
    Submodule.Quotient.mk (ComplexPoint.Basic.ComplexSchemePoint.formRestriction X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left)
      (originalAnalyticPreimageRestriction f i) p (HolomorphicPullback.originalKahlerFormPullback f U.unop p a))
  exact congrArg Submodule.Quotient.mk
    (LinearMap.congr_fun (originalKahlerFormPullback_restriction f i p) a)

/-- Actual pullback on the original degree-`p` presheaf of holomorphic forms. -/
def originalDeRhamPresheafPullback (f : X ⟶ Y) (p : ℕ) :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf Y (OAI.Topology.Dimension.Basic.TopologicalSpace.dim Y.left) p ⟶
      (TopCat.Presheaf.pushforward AddCommGrpCat (originalAnalyticSchemeMap f)).obj
        (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) p) where
  app U := AddCommGrpCat.ofHom (HolomorphicFormPullback.originalHolomorphicFormPullback f U.unop p).toAddMonoidHom
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro θ
    exact LinearMap.congr_fun (originalHolomorphicFormPullback_restriction f i p) θ

/-- The original exterior differential commutes with actual presheaf pullback. -/
theorem originalDeRhamPresheafPullback_differential (f : X ⟶ Y) (p : ℕ) :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential Y (OAI.Topology.Dimension.Basic.TopologicalSpace.dim Y.left) p ≫
        originalDeRhamPresheafPullback f (p + 1) =
      originalDeRhamPresheafPullback f p ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat (originalAnalyticSchemeMap f)).map
          (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) p) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro θ
  exact HolomorphicFormPullback.originalHolomorphicFormPullback_differential f U.unop p θ

/-- Actual scheme maps induce a morphism of the original presheaf de Rham complexes. -/
def originalDeRhamPresheafComplexPullback (f : X ⟶ Y) :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheafComplex Y (OAI.Topology.Dimension.Basic.TopologicalSpace.dim Y.left) ⟶
      ((TopCat.Presheaf.pushforward AddCommGrpCat (originalAnalyticSchemeMap f)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheafComplex X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left)) where
  f p := originalDeRhamPresheafPullback f p
  comm' i j hij := by
    obtain rfl := hij
    rw [Functor.mapHomologicalComplex_obj_d, ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheafComplex_d,
      ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheafComplex_d]
    exact (originalDeRhamPresheafPullback_differential f i).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DeRhamPresheafPullback
