import OAI.AlgebraicGeometry.ComplexMultiplication.CMGlobalSheafCycles
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ClosedHolomorphicClasses

/-! # Closed Global Representatives -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ClosedGlobalRepresentatives

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint
open scoped OAI.AlgebraicGeometry.Hodge.HolomorphicDeRham.ComplexPoint

/-! # Actual closed global holomorphic representatives of original F¹ -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Y" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
local notation "K" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left)
local notation "G" => OAI.AlgebraicGeometry.Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (Y) Ω•(X)
local notation "ΓInt" => Functor.mapHomologicalComplex
  (AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor (Y)) (ComplexShape.up ℤ)

/-- The actual cycle inclusion recovers exactly the retained original section. -/
theorem originalClosedHolomorphicGlobalCycle_iCycles (p : ℕ)
    (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (Opposite.op ⊤))
    (hθ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).hom.app (Opposite.op ⊤) θ = 0) :
    (G).iCycles (p : ℤ) (ClosedHolomorphicClasses.originalClosedHolomorphicGlobalCycle X p θ hθ) =
      CMGlobalSheafCycles.sheafExtendedGlobalSection (Y) (K) p θ := by
  change ((G).sc (p : ℤ)).iCycles (((G).sc (p : ℤ)).abCyclesIso.inv _) = _
  exact ((G).sc (p : ℤ)).abCyclesIso_inv_apply_iCycles _

set_option backward.isDefEq.respectTransparency false in
/-- Every actual original global cycle has an actual closed global holomorphic section. -/
theorem originalClosedHolomorphicGlobalCycle_surjective (p : ℕ) (c : (G).cycles (p : ℤ)) :
    ∃ (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (Opposite.op ⊤))
      (hθ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).hom.app (Opposite.op ⊤) θ = 0),
      ClosedHolomorphicClasses.originalClosedHolomorphicGlobalCycle X p θ hθ = c := by
  let ζ := (G).iCycles (p : ℤ) c
  let θ := CMGlobalSheafCycles.sheafRetainedGlobalSection (Y) (K) p ζ
  have hζ : (G).d (p : ℤ) ((p + 1 : ℕ) : ℤ) ζ = 0 := by
    simpa only [AddCommGrpCat.comp_apply, AddCommGrpCat.zero_apply] using!
      ConcreteCategory.congr_hom ((G).iCycles_d (p : ℤ) ((p + 1 : ℕ) : ℤ)) c
  have hθ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).hom.app (Opposite.op ⊤) θ = 0 := by
    simpa only [ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex_d] using!
      CMGlobalSheafCycles.sheafRetainedGlobalSection_closed (Y) (K) p ζ hζ
  refine ⟨θ, hθ, ?_⟩
  apply (AddCommGrpCat.mono_iff_injective ((G).iCycles (p : ℤ))).1 inferInstance
  rw [originalClosedHolomorphicGlobalCycle_iCycles]
  exact CMGlobalSheafCycles.sheafExtendedGlobalSection_retained (Y) (K) p ζ

/-- Every original global holomorphic cohomology class has such a closed section representative. -/
theorem originalClosedHolomorphicGlobalClass_surjective (p : ℕ) (z : (G).homology (p : ℤ)) :
    ∃ (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (Opposite.op ⊤))
      (hθ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).hom.app (Opposite.op ⊤) θ = 0),
      ClosedHolomorphicClasses.originalClosedHolomorphicGlobalClass X p θ hθ = z := by
  obtain ⟨c, hc⟩ := (AddCommGrpCat.epi_iff_surjective ((G).homologyπ (p : ℤ))).1 inferInstance z
  obtain ⟨θ, hθ, hcycle⟩ := originalClosedHolomorphicGlobalCycle_surjective X p c
  refine ⟨θ, hθ, ?_⟩
  change (G).homologyπ (p : ℤ) (ClosedHolomorphicClasses.originalClosedHolomorphicGlobalCycle X p θ hθ) = z
  rw [hcycle]
  exact hc

set_option backward.isDefEq.respectTransparency false in
/-- Original F¹ is exactly the original class image of actual closed global holomorphic one-forms. -/
theorem originalF1_mem_iff_closedGlobalSection (α : H_dR^1(X)) :
    α ∈ ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltrationComplexSubmodule X 1 1 ↔
      ∃ (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) 1).presheaf.obj (Opposite.op ⊤))
        (hθ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) 1).hom.app (Opposite.op ⊤) θ = 0),
        ClosedHolomorphicClasses.originalClosedHolomorphicDeRhamClass X 1 θ hθ = α := by
  constructor
  · intro hα
    obtain ⟨zf, hz⟩ := (FilteredGlobalClasses.originalF1_mem_iff_globalClass X α).mp hα
    let z := HomologicalComplex.homologyMap
      ((ΓInt).map (ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamInclusion X 1)) 1 zf
    have hg : GlobalNaturality.globalSectionsToHypercohomology X Ω•(X) 1 z = α :=
      (GlobalNaturality.globalSectionsToHypercohomology_naturality X
        (ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamInclusion X 1) 1 zf).trans hz
    obtain ⟨θ, hθ, hclass⟩ := originalClosedHolomorphicGlobalClass_surjective X 1 z
    exact ⟨θ, hθ,
      (congrArg (GlobalNaturality.globalSectionsToHypercohomology X Ω•(X) 1) hclass).trans hg⟩
  · rintro ⟨θ, hθ, rfl⟩
    exact ClosedHolomorphicClasses.originalClosedHolomorphicDeRhamClass_mem_filtration X 1 θ hθ

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ClosedGlobalRepresentatives
