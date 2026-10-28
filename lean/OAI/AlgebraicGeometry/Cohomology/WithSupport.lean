/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
This file has been modified.
-/
import OAI.AlgebraicTopology.Support.CohomologyFlasqueRestrict
import OAI.AlgebraicGeometry.Cohomology.AmbientInjectiveResolution
import OAI.AlgebraicGeometry.Cohomology.SupportedSingularModel
import OAI.AlgebraicGeometry.Cycle.TransportCohomologySheaf
import OAI.Algebra.Homology.Notation

/-! # With Support -/

namespace OAI.AlgebraicGeometry.Cohomology.WithSupport.ComplexPoint

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

open _root_.AlgebraicGeometry

/-!
# Cohomology of the analytic space with support in a closed set

`H^n_Z(X(ℂ); K)` is the sheaf cohomology of `X(ℂ)` with support in the closed set `Z` and
coefficients in the constant sheaf `K`. Forgetting the support lands in `H^n(X(ℂ); K)`. With
rational coefficients the group is computed by the sections supported in `Z` of the chosen
injective resolution of `ℚ`, or of the sheafified singular cochains.
-/

open _root_.CategoryTheory Limits _root_.TopologicalSpace

open OAI.AlgebraicGeometry.ComplexPoint.Basic.Point

variable (K : Type) [Field K] (X : Over (Spec ↧ℂ))

set_option quotPrecheck false in
/-- `H_[Z]^n(X; K)` is the sheaf cohomology of the analytic space `X(ℂ)` with support in the closed
set `Z ⊆ X(ℂ)` and coefficients in the constant sheaf `K`, in degree `n`. -/
scoped notation:max "H_[" Z "]^" n:max "(" X "; " K ")" =>
  AlgebraicTopology.Support.Cohomology.TopCat.Sheaf.supportH (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) Z
    ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).obj (AddCommGrpCat.of K)) n

variable (Z : Closeds (ComplexPoint.Basic.ComplexSchemePoint X))

/-- `H^n_Z(X(ℂ); K) → H^n(X(ℂ); K)`, forgetting the support. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.forgetSupport (n : ℕ) : H_[Z]^n(X; K) →+ H^n(X; K) :=
  (CategoryTheory.Sites.SheafCohomologyPair.Sheaf.H'.addEquivTerminal isTerminalTop _ n).toAddMonoidHom.comp
    (CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH.forget _ (homOfLE (le_top : Z.compl ≤ ⊤)) n)

/-- Forgetting the support `X(ℂ)` itself is injective. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.forgetSupport_injective_of_eq_top (hZ : Z = ⊤) (n : ℕ) :
    Function.Injective (ComplexPoint.Basic.ComplexSchemePoint.forgetSupport K X Z n) :=
  (CategoryTheory.Sites.SheafCohomologyPair.Sheaf.H'.addEquivTerminal isTerminalTop _ n).injective.comp
    (AlgebraicTopology.Support.Cohomology.TopCat.Sheaf.relH.forget_injective_of_eq_bot (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) _ _
      (by rw [hZ]; ext; simp) n)

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf in
/-- `H^n_Z(X(ℂ); ℚ) ≃ H^n(Γ_Z(X(ℂ), I))` for the chosen injective resolution `ℚ → I`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalSupportAddEquivSupportedInjectiveHomology (n : ℕ) :
    H_[Z]^n(X; ℚ) ≃+
      (((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation ↧(ComplexPoint.Basic.ComplexSchemePoint X) ⊤).mapHomologicalComplex ℤᵘᵖ).obj
        (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X Z)).homology n :=
  @AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) Z.compl ⊤
    Z.compl (top_inf_eq _) (ComplexPoint.Basic.ComplexSchemePoint.analyticHasExt X) _ (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X)
    (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex_isKInjective X)
    (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation X)
    (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation_quasiIso X) n

open OAI.AlgebraicTopology.Singular

variable [IsIntegral X.left] [Smooth X.hom]

/-- The augmentation `ℚ[0] → C^•` of the sheafified rational singular cochains on `X(ℂ)`, indexed
by integers. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalSingularAugmentation :
    (CochainComplex.singleFunctor (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) 0).obj 𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℚ) ⟶
      AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) :=
  (ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexIntIsoSingle ℚ X).inv ≫
    HomologicalComplex.extendMap
      (AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
      ComplexShape.embeddingUpNat

instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalSingularAugmentation_mono : Mono (ComplexPoint.Basic.ComplexSchemePoint.rationalSingularAugmentation X) := by
  dsimp only [ComplexPoint.Basic.ComplexSchemePoint.rationalSingularAugmentation]
  exact @mono_comp _ _ _ _ _ _ inferInstance _
    (AlgebraicTopology.Singular.SheafCochainResolution.constantsToSingularCochainComplexInt_mono ℚ (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))

instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalSingularAugmentation_quasiIso : QuasiIso (ComplexPoint.Basic.ComplexSchemePoint.rationalSingularAugmentation X) := by
  dsimp only [ComplexPoint.Basic.ComplexSchemePoint.rationalSingularAugmentation]
  have : QuasiIso (HomologicalComplex.extendMap
      (AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
      ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).mpr
      (AlgebraicTopology.Singular.SheafCochainResolution.constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℚ
        (ComplexPoint.Basic.ComplexSchemePoint.exists_contractibleOpen_le X))
  exact quasiIso_comp _ _ (hφ := quasiIso_of_isIso _) (hφ' := this)

variable [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf in
/-- `H^n_Z(X(ℂ); ℚ) ≃ H^n(Γ_Z(X(ℂ), C^•))` for the sheafified rational singular cochains `C^•`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.rationalSupportAddEquivSupportedSingularHomology (n : ℕ) :
    H_[Z]^n(X; ℚ) ≃+
      (((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation ↧(ComplexPoint.Basic.ComplexSchemePoint X) ⊤).mapHomologicalComplex ℤᵘᵖ).obj
        (AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) Z.compl)).homology n :=
  letI : ∀ V : Opens (ComplexPoint.Basic.ComplexSchemePoint X), ParacompactSpace V := ComplexPoint.Basic.ComplexSchemePoint.openParacompactSpace X
  @AlgebraicTopology.Support.CohomologyFlasqueModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomologyOfFlasque (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
    𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℚ) (AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
    (AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex_isStrictlyGE _) (ComplexPoint.Basic.ComplexSchemePoint.rationalSingularAugmentation X)
    (ComplexPoint.Basic.ComplexSchemePoint.rationalSingularAugmentation_mono X) (ComplexPoint.Basic.ComplexSchemePoint.rationalSingularAugmentation_quasiIso X)
    Z.compl ⊤ Z.compl (top_inf_eq _)
    (fun n => AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex_isFlasque (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n)
    (ComplexPoint.Basic.ComplexSchemePoint.analyticHasExt X) n

end

end OAI.AlgebraicGeometry.Cohomology.WithSupport.ComplexPoint
