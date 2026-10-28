/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.Algebra.Homology.Notation
import OAI.AlgebraicTopology.Support.SingularFlasqueOn
import OAI.AlgebraicGeometry.Cohomology.AmbientInjectiveResolution
import OAI.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
import OAI.AlgebraicGeometry.ComplexPoint.ProjectiveParacompact

/-! # Supported Singular Model -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Supported singular models on smooth projective complex varieties

The generic supported singular/injective comparison is specialized using the analytic
contractible neighborhoods and hereditary paracompactness of smooth projective analytifications.
Only the geometric scheme hypotheses remain. The target is the ambient injective complex used by
the derived rational support comparison.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom]

/-- Let `X` be a smooth integral complex scheme and `U ⊆ X(ℂ)` an analytic open. Write `C^•` for the
sheafified rational singular cochains and `ℚ → I^•` for the chosen injective resolution. This
map `Γ_{X(ℂ) \ U}(C^•) → Γ_{X(ℂ) \ U}(I^•)` restricts the augmentation-preserving resolution
comparison to subsheaves of sections vanishing on `U`. -/
def ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularToAmbientInjective
    (U : Opens (ComplexPoint.Basic.ComplexSchemePoint X)) :
    -- `Γ_{X(ℂ) \ U}` of the singular-cochain model, mapping to `Γ_{X(ℂ) \ U}(I^•)`.
    AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) U ⟶
      ((AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside
        -- `X(ℂ)`.
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) U).mapHomologicalComplex ℤᵘᵖ).obj
          -- The injective resolution `I^•` of `ℚ` on `X(ℂ)`.
          (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X) :=
  AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedSingularToInjectiveComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
    (ComplexPoint.Basic.ComplexSchemePoint.exists_contractibleOpen_le X) U

variable [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

/-- The supported comparison is a sheaf quasi-isomorphism under
the usual smooth projective geometry hypotheses alone. -/
instance ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularToAmbientInjective_quasiIso
    (U : Opens (ComplexPoint.Basic.ComplexSchemePoint X)) :
    QuasiIso (ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularToAmbientInjective X U) := by
  let : ∀ V : Opens (ComplexPoint.Basic.ComplexSchemePoint X), ParacompactSpace V :=
    ComplexPoint.Basic.ComplexSchemePoint.openParacompactSpace X
  exact AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedSingularToInjectiveComplex_quasiIso
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) (ComplexPoint.Basic.ComplexSchemePoint.exists_contractibleOpen_le X) U

end

end OAI.AlgebraicGeometry
