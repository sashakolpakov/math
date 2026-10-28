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
import OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution
import OAI.AlgebraicGeometry.Hodge.Filtration
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import OAI.Algebra.Homology.Notation

/-! # Ambient Injective Resolution -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# The chosen injective resolution of the constant rational sheaf

`ℚ → I^•` is a chosen injective resolution of the constant rational sheaf on the analytic space
`X(ℂ)`, indexed by integers. It is K-injective.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable (X : Over (Spec ↧ℂ))

/-- Let `X` be a scheme over `ℂ`. This is the complex `I^•` of sheaves of abelian groups in a chosen
injective resolution `ℚ → I^•` on the analytic space `X(ℂ)`. It is indexed by integers and is
zero in negative degrees. -/
def ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex :
    CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ :=
  -- An injective resolution `ℚ_{X(ℂ)} → I^•`.
  (AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) (AddCommGrpCat.of ℚ)).cocomplex.extend
      ComplexShape.embeddingUpNat

/-- Let `X` be a scheme over `ℂ`. This is the augmentation `ℚ[0] → I^•` of the chosen injective
resolution of the constant rational sheaf on the analytic space `X(ℂ)`, with both complexes
indexed by integers. -/
def ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveAugmentation :
    ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt ℚ X ⟶
      ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X :=
  HomologicalComplex.extendMap
    (AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) (AddCommGrpCat.of ℚ)).ι
    ComplexShape.embeddingUpNat

instance ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveAugmentation_quasiIso :
    QuasiIso (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveAugmentation X) := by
  let I := AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) (AddCommGrpCat.of ℚ)
  let : QuasiIso I.ι := I.quasiIso
  exact (HomologicalComplex.quasiIso_extendMap_iff I.ι _).mpr inferInstance

instance ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex_injective (q : ℤ) :
    Injective ((ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X).X q) :=
  OAI.Algebra.Homology.LiftToInjective.CochainComplex.injective_extend_nat _
    (AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat.ambientConstantInjectiveResolution
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) (AddCommGrpCat.of ℚ)).injective q

instance ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex_isStrictlyGE :
    (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X).IsStrictlyGE 0 := by
  dsimp only [ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex]
  infer_instance

local instance ComplexPoint.Basic.ComplexSchemePoint.rationalConeForgetSheafDerivedCategory :
    HasDerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)

instance ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex_isKInjective :
    (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X).IsKInjective :=
  CochainComplex.isKInjective_of_injective _ 0

/-- The augmentation `ℚ[0] → I^•`, with the source the constant sheaf placed in degree zero. -/
def ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation :
    (CochainComplex.singleFunctor (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) 0).obj 𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℚ) ⟶
      ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X :=
  (ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexIntIsoSingle ℚ X).inv ≫ ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveAugmentation X

instance ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation_quasiIso :
    QuasiIso (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation X) := by
  dsimp only [ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveSingleAugmentation]
  infer_instance

end

end OAI.AlgebraicGeometry
