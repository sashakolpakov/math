/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.Algebra.Homology.Notation
import OAI.AlgebraicTopology.Support.SingularFlasqueModel

/-! # Singular Flasque On -/

namespace OAI.AlgebraicTopology.Support.SingularFlasqueOn.Singular

noncomputable section

/-!
# Constructions used only in proofs

-/

open _root_.CategoryTheory Limits _root_.TopologicalSpace _root_.HomologicalComplex

variable (X : TopCat.{0})

variable (hX : ∀ (x : X) (V : Opens X), x ∈ V →
  ∃ (W : Opens X), x ∈ W ∧ ContractibleSpace W ∧ W ≤ V)

variable [T2Space X] [∀ V : Opens X, ParacompactSpace V]

/-- The comparison is a quasi-isomorphism on sections on every open set.
This stronger conclusion is essential for applying local normal-slice calculations. -/
theorem supportedSingularToInjectiveComplex_onOpen_quasiIso (U V : Opens X) :
    QuasiIso (((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
      (SingularFlasqueModel.Singular.supportedSingularToInjectiveComplex X hX U)) :=
  FlasqueComparison.TopCat.Sheaf.supportedSections_map_quasiIso_of_flasque X U V
    (SingularFlasqueModel.Singular.singularToConstantInjectiveComplex X hX) 0 0 (fun _ => inferInstance) (fun _ => inferInstance)

/-- Let `X` be Hausdorff, with every open subset paracompact, and with a basis of contractible open
neighborhoods. Let `C` be the sheafified rational singular cochain complex and `I` an injective
resolution of the constant rational sheaf. For opens `U,V ⊆ X`, the augmentation-preserving
comparison `C → I` induces this isomorphism `H^n(Γ_{X \ U}(V,C)) ≅ H^n(Γ_{X \ U}(V,I))`. Here
supported sections on `V` are sections vanishing on `V ∩ U`, and `n` is any integer. -/
def supportedSingularInjectiveHomologyIso (U V : Opens X) (n : ℤ) :
    ((((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
      (SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex X U))).homology n ≅
    ((((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
      (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj
        (SingularFlasqueModel.Singular.rationalConstantInjectiveComplex X)))).homology n :=
  let f := ((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
    (SingularFlasqueModel.Singular.supportedSingularToInjectiveComplex X hX U)
  letI : QuasiIso f := supportedSingularToInjectiveComplex_onOpen_quasiIso X hX U V
  asIso (HomologicalComplex.homologyMap f n)

end

end OAI.AlgebraicTopology.Support.SingularFlasqueOn.Singular
