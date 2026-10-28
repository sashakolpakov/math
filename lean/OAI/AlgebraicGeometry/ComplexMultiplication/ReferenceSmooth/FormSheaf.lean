import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.OpenForms
import OAI.AlgebraicGeometry.Hodge.HolomorphicDeRham
import OAI.Analysis.DifferentialForms.Manifold.SheafDeRham

/-! # Form Sheaf -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.FormSheaf

noncomputable section

/-! # A genuine sheaf-complex map from the original holomorphic forms

The degreewise map extends the actual original quotient evaluation. The sheaf
condition and exterior differential are those of actual smooth tangent forms.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Model" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "J" => Opens.grothendieckTopology (TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))

/-- Forgetting complex scalars on actual smooth form sheaves. -/
def originalSmoothFormSheafForget :
    TopCat.Sheaf (ModuleCat ℂ) (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ⥤
      TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) :=
  sheafCompose J (forget₂ (ModuleCat ℂ) AddCommGrpCat)

instance originalSmoothFormSheafForget_additive : (originalSmoothFormSheafForget X).Additive where
  map_add := rfl

/-- The actual sheaf of smooth tangent p-forms with its additive structure. -/
def originalSmoothFormAddSheaf (p : ℕ) :
    TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) :=
  (originalSmoothFormSheafForget X).obj (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf Model (ComplexPoint.Basic.ComplexSchemePoint X) p)

/-- Original quotient evaluation defines a natural map on the actual form presheaves. -/
def originalHolomorphicToSmoothPresheaf (p : ℕ) :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p ⟶
      (originalSmoothFormAddSheaf X p).presheaf where
  app U := AddCommGrpCat.ofHom
    (OpenForms.originalHolomorphicToSmoothOpenForm X U.unop p).toAddMonoidHom
  naturality U V h := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro θ
    exact OpenForms.originalHolomorphicToSmoothOpenForm_restrict X (leOfHom h.unop) p θ

/-- The natural quotient evaluation preserves the actual presheaf differential. -/
theorem originalHolomorphicToSmoothPresheaf_differential (p : ℕ) :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p ≫
        originalHolomorphicToSmoothPresheaf X (p + 1) =
      originalHolomorphicToSmoothPresheaf X p ≫
        ((originalSmoothFormSheafForget X).map
          (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheafD Model (ComplexPoint.Basic.ComplexSchemePoint X) p)).hom := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro θ
  exact (OpenForms.originalHolomorphicToSmoothOpenForm_differential X U.unop p θ).symm

/-- The original sheafification maps to the actual smooth form sheaf. -/
def originalHolomorphicToSmoothSheaf (p : ℕ) :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p ⟶ originalSmoothFormAddSheaf X p :=
  ⟨sheafifyLift J (originalHolomorphicToSmoothPresheaf X p)
    (originalSmoothFormAddSheaf X p).property⟩

/-- The sheaf map retains precisely the original quotient evaluation. -/
theorem originalHolomorphicToSmoothSheaf_unit (p : ℕ) :
    toSheafify J (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p) ≫
      (originalHolomorphicToSmoothSheaf X p).hom =
        originalHolomorphicToSmoothPresheaf X p :=
  toSheafify_sheafifyLift _ _ _

/-- Exterior differentiation is retained after the original sheafification. -/
theorem originalHolomorphicToSmoothSheaf_differential (p : ℕ) :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p ≫
        originalHolomorphicToSmoothSheaf X (p + 1) =
      originalHolomorphicToSmoothSheaf X p ≫
        (originalSmoothFormSheafForget X).map
          (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheafD Model (ComplexPoint.Basic.ComplexSchemePoint X) p) := by
  apply CategoryTheory.Sheaf.hom_ext
  change sheafifyMap J (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p) ≫
      sheafifyLift J (originalHolomorphicToSmoothPresheaf X (p + 1))
        (originalSmoothFormAddSheaf X (p + 1)).property =
    sheafifyLift J (originalHolomorphicToSmoothPresheaf X p)
      (originalSmoothFormAddSheaf X p).property ≫
        ((originalSmoothFormSheafForget X).map
          (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheafD Model (ComplexPoint.Basic.ComplexSchemePoint X) p)).hom
  exact (sheafifyMap_sheafifyLift J _ _ _).trans
    ((congrArg (fun η => sheafifyLift J η (originalSmoothFormAddSheaf X (p + 1)).property)
      (originalHolomorphicToSmoothPresheaf_differential X p)).trans
        (sheafifyLift_comp J _ _ _ _))

/-- The original holomorphic de Rham complex maps to genuine smooth tangent forms. -/
def originalHolomorphicToSmoothSheafComplex :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) ⟶
      ((originalSmoothFormSheafForget X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex Model (ComplexPoint.Basic.ComplexSchemePoint X)) where
  f p := originalHolomorphicToSmoothSheaf X p
  comm' i j hij := by
    obtain rfl := hij
    rw [Functor.mapHomologicalComplex_obj_d, ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex_d,
      Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex_d]
    exact (originalHolomorphicToSmoothSheaf_differential X i).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.FormSheaf
