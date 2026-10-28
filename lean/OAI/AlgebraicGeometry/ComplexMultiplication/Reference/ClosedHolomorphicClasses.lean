import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalFiltration
import OAI.AlgebraicGeometry.ComplexMultiplication.CMGlobalSheafCycles
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AbelianInvariantClosed

/-! # Closed Holomorphic Classes -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ClosedHolomorphicClasses

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint
open scoped OAI.AlgebraicGeometry.Hodge.HolomorphicDeRham.ComplexPoint

/-! # Actual closed original global holomorphic forms define original filtered classes -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

set_option backward.isDefEq.respectTransparency false in
/-- The actual cycle associated to a closed original holomorphic global section. -/
def originalClosedHolomorphicGlobalCycle (p : ℕ)
    (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (Opposite.op ⊤))
    (hθ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).hom.app (Opposite.op ⊤) θ = 0) :
    (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) Ω•(X)).cycles (p : ℤ) :=
  let K := ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X (Topology.Dimension.Basic.TopologicalSpace.dim X.left)
  let G := Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) Ω•(X)
  (G.sc (p : ℤ)).abCyclesIso.inv
    ⟨CMGlobalSheafCycles.sheafExtendedGlobalSection (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) K p θ, by
      change G.d (p : ℤ) ((ComplexShape.up ℤ).next (p : ℤ))
        (CMGlobalSheafCycles.sheafExtendedGlobalSection (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) K p θ) = 0
      have hn : (ComplexShape.up ℤ).next (p : ℤ) = ((p + 1 : ℕ) : ℤ) :=
        ComplexShape.next_eq' (ComplexShape.up ℤ) (by simp)
      rw [hn]
      exact CMGlobalSheafCycles.sheafExtendedGlobalSection_closed (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) K p θ
        (by simpa only [K, ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex_d] using! hθ)⟩

/-- The genuine original global cohomology class of that closed section. -/
def originalClosedHolomorphicGlobalClass (p : ℕ)
    (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (Opposite.op ⊤))
    (hθ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).hom.app (Opposite.op ⊤) θ = 0) :
    (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) Ω•(X)).homology (p : ℤ) :=
  (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) Ω•(X)).homologyπ
    (p : ℤ) (originalClosedHolomorphicGlobalCycle X p θ hθ)

/-- Its class in the unchanged original de Rham hypercohomology. -/
def originalClosedHolomorphicDeRhamClass (p : ℕ)
    (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (Opposite.op ⊤))
    (hθ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).hom.app (Opposite.op ⊤) θ = 0) :
    H_dR^(p : ℤ)(X) :=
  GlobalNaturality.globalSectionsToHypercohomology X Ω•(X) (p : ℤ)
    (originalClosedHolomorphicGlobalClass X p θ hθ)

/-- No filtration hypothesis is required: this actual class belongs to original Fᵖ. -/
theorem originalClosedHolomorphicDeRhamClass_mem_filtration (p : ℕ)
    (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (Opposite.op ⊤))
    (hθ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).hom.app (Opposite.op ⊤) θ = 0) :
    originalClosedHolomorphicDeRhamClass X p θ hθ ∈ ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltration X (p : ℤ) (p : ℤ) :=
  GlobalFiltration.originalGlobalDeRhamClass_mem_filtration X (p : ℤ) _

variable [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X]

local notation "N" =>
  (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)

/-- Every actual native invariant complex covector defines an original de Rham class. -/
def originalAbelianInvariantDeRhamClass (α : N →L[ℂ] ℂ) : H_dR^1(X) :=
  originalClosedHolomorphicDeRhamClass X 1 (AbelianInvariantGlobal.originalAbelianInvariantGlobalSection X α)
    (AbelianInvariantClosed.originalAbelianInvariantGlobalSection_closed X α)

/-- The constructed invariant class lies in the actual original F¹ of H¹. -/
theorem originalAbelianInvariantDeRhamClass_mem_F1 (α : N →L[ℂ] ℂ) :
    originalAbelianInvariantDeRhamClass X α ∈ ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltrationComplexSubmodule X 1 1 :=
  originalClosedHolomorphicDeRhamClass_mem_filtration X 1 _ _

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ClosedHolomorphicClasses
