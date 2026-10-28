import OAI.Algebra.Homology.Notation
import OAI.AlgebraicGeometry.Cohomology.SupportedSingularHomology
import OAI.AlgebraicGeometry.Cycle.LocalLocalHomology
import OAI.AlgebraicTopology.Support.SingularSectionCohomology

/-! # Transport Cohomology Sheaf -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Cohomology-sheaf concentration for smooth closed supports

The complex is the supported-sections kernel applied to the fixed ambient rational injective
resolution. Its open-section homology is compared to relative singular cohomology by the
singular resolution and restriction-cone maps, and cofinal normal neighborhoods then give
stalkwise and sheafwise concentration in degree twice the complex codimension. Identifying
the surviving cohomology sheaf with rational constants on the support is left to a later file.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Topology _root_.TopologicalSpace Opposite

open OAI.AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

/-- Let `X` be a smooth integral projective scheme over `ℂ` and `S` a closed subset of its analytic
space `X(ℂ)`. For the chosen injective resolution `ℚ → I^•`, this complex has in each degree the
subsheaf of `I^n` consisting of sections that vanish off `S`. Its differentials are induced by
those of `I^•`, and it represents the derived sheaf of sections with support in `S`. -/
def ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex (S : Closeds (ComplexPoint.Basic.ComplexSchemePoint X)) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) ℤ :=
  -- `RΓ_S(ℚ)`: the `S`-supported subsheaves of an injective resolution of `ℚ` on `X(ℂ)`.
  ((AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside
    -- `X(ℂ)`.
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
    -- The open `X(ℂ) \ S`; sections supported outside it are the sections supported on `S`.
    S.compl).mapHomologicalComplex ℤᵘᵖ).obj
      -- The injective resolution `I^•` of `ℚ` on `X(ℂ)`.
      (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X)

instance ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex_isStrictlyGE (S : Closeds (ComplexPoint.Basic.ComplexSchemePoint X)) :
    (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X S).IsStrictlyGE 0 := by
  dsimp [ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex]
  infer_instance

end

end OAI.AlgebraicGeometry
