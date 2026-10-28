import OAI.Algebra.Homology.Notation
import OAI.AlgebraicGeometry.Cycle.TransportCohomologySheaf

/-! # Transport Cohomology Section -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Cohomology-sheaf concentration for smooth closed supports

-/

/-! ### Constructions used only in proofs -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Topology _root_.TopologicalSpace Opposite

open OAI.AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

/-- Let `X` be a smooth integral projective scheme over `ℂ`, `Y = X(ℂ)` with its analytic topology,
`S ⊆ Y` closed, and `V ⊆ Y` open. For an injective resolution `I` of the constant rational
sheaf, this additive equivalence identifies `H^n(Γ_S(V,I))` with relative singular cohomology
`H^n(V,V \ S;ℚ)`. Here `Γ_S(V,I^q)` consists of sections over `V` that vanish off `S`. -/
def ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv (S : Closeds (ComplexPoint.Basic.ComplexSchemePoint X))
    (V : Opens (ComplexPoint.Basic.ComplexSchemePoint X)) (n : ℕ) :
    ((((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) V).mapHomologicalComplex
      ℤᵘᵖ).obj (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X S))).homology (n : ℤ) ≃+
        AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair
          (V : Set (ComplexPoint.Basic.ComplexSchemePoint X)) (S : Set (ComplexPoint.Basic.ComplexSchemePoint X))) n :=
  letI : ∀ W : Opens (ComplexPoint.Basic.ComplexSchemePoint X), ParacompactSpace W := ComplexPoint.Basic.ComplexSchemePoint.openParacompactSpace X
  (ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularInjectiveHomologyIso X S.compl V (n : ℤ)).symm.addCommGroupIsoToAddEquiv
    |>.trans (AlgebraicTopology.Support.SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivSupportComplement
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S S.isClosed V n)

end

end OAI.AlgebraicGeometry
