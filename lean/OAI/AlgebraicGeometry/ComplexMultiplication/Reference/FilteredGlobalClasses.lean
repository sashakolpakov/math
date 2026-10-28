import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.LowestDegreeClasses
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredPullback

/-! # Filtered Global Classes -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredGlobalClasses

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint
open scoped OAI.AlgebraicGeometry.Hodge.HolomorphicDeRham.ComplexPoint

/-! # Original F¹ classes are represented by global holomorphic-form classes

The unchanged original filtered complex has no terms below its filtration
degree. Its hypercohomology in that degree therefore comes from actual global
cohomology classes, using the original inclusion and original comparison.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

/-- The original filtered complex is supported in its original form degrees. -/
theorem originalFilteredDeRham_isStrictlyGE (p : ℤ) : (F^p Ω•(X)).IsStrictlyGE p :=
  inferInstanceAs (HomologicalComplex.IsStrictlySupported
    (Ω•(X).stupidTrunc (ComplexShape.embeddingUpIntGE p)) (ComplexShape.embeddingUpIntGE p))

/-- Actual global classes in the lowest filtered degree, mapped through the original inclusion. -/
def originalLowestDegreeGlobalDeRhamClass (p : ℤ) :
    (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) (F^p Ω•(X))).homology p →+
      H_dR^p(X) :=
  (ComplexPoint.Basic.ComplexSchemePoint.filteredToDeRhamCohomology X p p).comp
    (GlobalNaturality.globalSectionsToHypercohomology X (F^p Ω•(X)) p)

/-- The original filtration in its lowest degree is exactly the image of actual global classes. -/
theorem originalHodgeFiltration_mem_iff_globalClass (p : ℤ) (α : H_dR^p(X)) :
    α ∈ ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltration X p p ↔
      ∃ z : (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) (F^p Ω•(X))).homology p,
        originalLowestDegreeGlobalDeRhamClass X p z = α := by
  let : (F^p Ω•(X)).IsStrictlyGE p := originalFilteredDeRham_isStrictlyGE X p
  constructor
  · rintro ⟨β, rfl⟩
    obtain ⟨z, hz⟩ := LowestDegreeClasses.globalSectionsToHypercohomology_surjective_of_isStrictlyGE
      X (F^p Ω•(X)) p β
    exact ⟨z, congrArg (ComplexPoint.Basic.ComplexSchemePoint.filteredToDeRhamCohomology X p p) hz⟩
  · rintro ⟨z, rfl⟩
    exact ⟨GlobalNaturality.globalSectionsToHypercohomology X (F^p Ω•(X)) p z, rfl⟩

/-- In particular, unchanged original F¹ in H¹ consists of actual global holomorphic classes. -/
theorem originalF1_mem_iff_globalClass (α : H_dR^1(X)) :
    α ∈ ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltrationComplexSubmodule X 1 1 ↔
      ∃ z : (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) (F^1 Ω•(X))).homology 1,
        originalLowestDegreeGlobalDeRhamClass X 1 z = α :=
  originalHodgeFiltration_mem_iff_globalClass X 1 α

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredGlobalClasses
