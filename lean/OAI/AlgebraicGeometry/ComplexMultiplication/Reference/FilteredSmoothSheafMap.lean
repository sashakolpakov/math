import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Filtration
import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.SmoothComplex

/-! # Filtered Smooth Sheaf Map -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredSmoothSheafMap

noncomputable section

/-! # Original holomorphic sections map to the actual filtered smooth sheaf -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "M" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X

/-- The map uses exactly the values of the original holomorphic-to-smooth map. -/
def originalHolomorphicToFilteredSmoothSheaf (q : ℕ) (r : ℤ) (hr : r ≤ (q : ℤ)) :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) q ⟶
      (ReferenceSmooth.FormSheaf.originalSmoothFormSheafForget X).obj
        (Comparison.Betti.Filtered.SmoothComplex.Hodge.filteredFormSheaf E M q r) :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun θ := ⟨ReferenceSmooth.Local.originalHolomorphicToSmoothSheafSection X q U.unop θ,
            ReferenceSmooth.Filtration.originalHolomorphicSmoothSection_filtered X q U.unop θ r hr⟩
          map_zero' := Subtype.ext (map_zero _)
          map_add' θ η := Subtype.ext (map_add _ θ η) }
      naturality {U V} f := by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro θ
        apply Subtype.ext
        exact NatTrans.naturality_apply (ReferenceSmooth.FormSheaf.originalHolomorphicToSmoothSheaf X q).hom f θ }

/-- Forgetting the filtration recovers precisely the original sheaf map. -/
theorem originalHolomorphicToFilteredSmoothSheaf_comp_inclusion
    (q : ℕ) (r : ℤ) (hr : r ≤ (q : ℤ)) :
    originalHolomorphicToFilteredSmoothSheaf X q r hr ≫
        (ReferenceSmooth.FormSheaf.originalSmoothFormSheafForget X).map
          (Comparison.Betti.Filtered.SmoothComplex.Hodge.filteredFormSheafInclusion E M q r) =
      ReferenceSmooth.FormSheaf.originalHolomorphicToSmoothSheaf X q := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro θ
  rfl

/-- The actual filtered differential retains the original holomorphic differential. -/
theorem originalHolomorphicToFilteredSmoothSheaf_differential
    (q : ℕ) (r : ℤ) (hr : r ≤ (q : ℤ)) :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) q ≫
        originalHolomorphicToFilteredSmoothSheaf X (q + 1) r (by omega) =
      originalHolomorphicToFilteredSmoothSheaf X q r hr ≫
        (ReferenceSmooth.FormSheaf.originalSmoothFormSheafForget X).map
          (Comparison.Betti.Filtered.SmoothComplex.Hodge.filteredFormSheafD E M q r) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro θ
  apply Subtype.ext
  exact congrArg (fun f => f.hom.app U θ)
    (ReferenceSmooth.FormSheaf.originalHolomorphicToSmoothSheaf_differential X q)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredSmoothSheafMap
