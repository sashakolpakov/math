/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.Algebra.Homology.Notation
import OAI.AlgebraicGeometry.Cohomology.SupportedSingularModel

/-! # Supported Singular Homology -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Supported singular models on smooth projective complex varieties

-/

/-! ### Constructions used only in proofs -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom]

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `Y = X(ℂ)` its analytic topology. This
cochain map sends the sheafified rational singular cochain complex on `Y` to the chosen
injective resolution of the constant rational sheaf. It extends the identity on constant
cochains and uses local contractibility of `Y`. -/
def ComplexPoint.Basic.ComplexSchemePoint.complexSingularToAmbientInjective :
    AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ⟶
      ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X :=
  AlgebraicTopology.Support.SingularFlasqueModel.Singular.singularToConstantInjectiveComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
    (ComplexPoint.Basic.ComplexSchemePoint.exists_contractibleOpen_le X)

instance ComplexPoint.Basic.ComplexSchemePoint.complexSingularToAmbientInjective_quasiIso :
    QuasiIso (ComplexPoint.Basic.ComplexSchemePoint.complexSingularToAmbientInjective X) :=
  AlgebraicTopology.Support.SingularFlasqueModel.Singular.singularToConstantInjectiveComplex_quasiIso _ _

variable [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

/-- Let `X` be a smooth integral scheme over `ℂ`, and give `Y = X(ℂ)` its analytic topology. Assume
also that `X` is projective, and let `U,V ⊆ Y` be open. The comparison from sheafified rational
singular cochains `C` to a constant-sheaf injective resolution `I` induces this isomorphism
`H^n(Γ_{Y \ U}(V,C)) ≅ H^n(Γ_{Y \ U}(V,I))` for every integer `n`. In each complex, sections
over `V` are required to vanish on `V ∩ U`. -/
def ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularInjectiveHomologyIso
    (U V : Opens (ComplexPoint.Basic.ComplexSchemePoint X)) (n : ℤ) :
    ((((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) V).mapHomologicalComplex
      ℤᵘᵖ).obj
        (AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) U))).homology n ≅
    ((((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) V).mapHomologicalComplex
      ℤᵘᵖ).obj
        (((AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside
          (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) U).mapHomologicalComplex ℤᵘᵖ).obj
            (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X)))).homology n :=
  letI : ∀ W : Opens (ComplexPoint.Basic.ComplexSchemePoint X), ParacompactSpace W :=
    ComplexPoint.Basic.ComplexSchemePoint.openParacompactSpace X
  AlgebraicTopology.Support.SingularFlasqueOn.Singular.supportedSingularInjectiveHomologyIso (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
    (ComplexPoint.Basic.ComplexSchemePoint.exists_contractibleOpen_le X) U V n

end

end OAI.AlgebraicGeometry
