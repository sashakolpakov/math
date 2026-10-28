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
import OAI.AlgebraicTopology.Singular.SheafCochainRestriction
import OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain

/-! # Global Restriction -/

namespace OAI.AlgebraicTopology.Singular.GlobalRestriction

noncomputable section

/-!
# Global singular restriction

This file identifies the top-open comparison with the chosen sheafification unit and proves
that global singular restriction commutes strictly with that unit. This is the naturality square
needed to compare a support cone built from singular-cochain sheaves with the corresponding raw
singular-cochain cone.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

variable (R : Type) [CommRing R] {U X : TopCat.{0}} (j : U ⟶ X)

/-- Restriction of the raw singular-cochain presheaf complexes. -/
def singularRawRestrictionComplex :
    SheafCochain.singularCochainPresheafComplex R X ⟶
      ((Functor.whiskeringLeft _ _ _).obj (Opens.map j).op).mapHomologicalComplex
        (ComplexShape.up ℕ) |>.obj (SheafCochain.singularCochainPresheafComplex R U) where
  f n := SheafCochainRestriction.singularRestrictionToRawPushforward R j n
  comm' i k hik := by
    obtain rfl := hik
    rw [SheafCochain.singularCochainPresheafComplex_d, Functor.mapHomologicalComplex_obj_d,
      SheafCochain.singularCochainPresheafComplex_d]
    exact (SheafCochainRestriction.singularRestrictionToRawPushforward_coboundary R j i).symm

/-- Raw singular cochains on the inverse image of the top open. -/
def globalRawPushforwardSingularCochainComplex : CochainComplex AddCommGrpCat ℕ :=
  ((((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op (⊤ : Opens X))).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
    ((((Functor.whiskeringLeft _ _ _).obj (Opens.map j).op).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (SheafCochain.singularCochainPresheafComplex R U)))

/-- Global sections of the pushforward singular-cochain sheaf complex. -/
def globalPushforwardSingularCochainSheafComplex : CochainComplex AddCommGrpCat ℕ :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj
      (((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (((TopCat.Sheaf.pushforward AddCommGrpCat j).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj (SheafCochain.singularCochainSheafComplex R U)))

/-- Restriction of raw global singular cochains to the inverse image of the top open. -/
def globalRawSingularRestriction :
    SheafSubdivisionCochain.globalRawSingularCochainComplex R X ⟶
      globalRawPushforwardSingularCochainComplex R j :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (singularRawRestrictionComplex R j)

/-- Restriction on the global-section complexes of singular-cochain sheaves. -/
def globalSingularSheafRestriction :
    SheafSubdivisionCochain.globalSingularCochainSheafComplex R X ⟶
      globalPushforwardSingularCochainSheafComplex R j :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map
      (((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (SheafCochainRestriction.singularRestrictionSheafComplex R j))

/-- The sheafification unit evaluated after restriction to the inverse image of the top open. -/
def globalRawPushforwardToSingularSheaf :
    globalRawPushforwardSingularCochainComplex R j ⟶
      globalPushforwardSingularCochainSheafComplex R j :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map
      ((((Functor.whiskeringLeft _ _ _).obj (Opens.map j).op).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (SheafCochain.singularCochainSheafificationUnit R U))

/-- The double-plus presentation of the comparison is the chosen sheafification unit in each
degree. -/
lemma topOpenToGlobalSingularCochainSheafComplex_f (n : ℕ) :
    (SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex R X).f n =
      (toSheafify (Opens.grothendieckTopology X)
        (SheafCochain.singularCochainPresheaf R X n)).app (.op ⊤) := by
  change ((SheafSubdivisionCochain.singularCochainToPlusPlusPresheafComplex R X).f n ≫
      (SheafSubdivisionCochain.singularCochainPlusPlusPresheafComplexIsoSheafComplex R X).hom.f n).app
        (.op ⊤) = _
  rw [SheafSubdivisionCochain.singularCochainToPlusPlusPresheafComplex_f]
  change ((Opens.grothendieckTopology X).toSheafify
      (SheafCochain.singularCochainPresheaf R X n) ≫
    (plusPlusIsoSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat (SheafCochain.singularCochainPresheaf R X n)).hom).app (.op ⊤) = _
  rw [toSheafify_plusPlusIsoSheafify_hom]

/-- Global restriction commutes strictly with sheafification. -/
lemma globalSingularSheafRestriction_naturality :
    SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex R X ≫
        globalSingularSheafRestriction R j =
      globalRawSingularRestriction R j ≫
        globalRawPushforwardToSingularSheaf R j := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    topOpenToGlobalSingularCochainSheafComplex_f]
  exact congrArg (fun f ↦ f.app (.op ⊤))
    (SheafCochainRestriction.toSheafify_comp_singularRestrictionSheaf R j n)

end

end OAI.AlgebraicTopology.Singular.GlobalRestriction
