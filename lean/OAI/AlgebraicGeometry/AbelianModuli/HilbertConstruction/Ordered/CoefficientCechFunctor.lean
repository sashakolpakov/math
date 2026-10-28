/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FormalCoproductEvaluationAdditive
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PresheafAdditive

/-! # Coefficient Cech Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechFunctor

noncomputable section

/-!
# Functoriality of ordered base-linear Cech complexes

This file makes the ordered base-linear Cech complex functorial in the scheme module.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive
  Opposite TopologicalSpace

universe u

/-- The degree-`n` term of the ordered base-linear Cech complex, functorially in the
scheme module. -/
noncomputable def orderedCoefficientCechObjectFunctor
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (n : ℕ) :
    X.Modules ⥤ ModuleCat.{u} R :=
  Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c ⋙
    FormalCoproduct.evalOp X.Opens
      (ModuleCat.{u} R) ⋙
    (CategoryTheory.evaluation ((FormalCoproduct.{u} X.Opens)ᵒᵖ)
      (ModuleCat.{u} R)).obj
        (op (SectionCechIndices.orderedCechFormalObject U n))

@[simp]
theorem orderedCoefficientCechObjectFunctor_obj
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (n : ℕ) (M : X.Modules) :
    (orderedCoefficientCechObjectFunctor c U n).obj M =
      CoefficientCechTerms.orderedCoefficientCechObject c M U n :=
  rfl

instance orderedCoefficientCechObjectFunctor_additive
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (n : ℕ) :
    (orderedCoefficientCechObjectFunctor c U n).Additive := by
  have : (Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).Additive := Coefficient.PresheafAdditive.coefficientModulePresheafFunctor_additive c
  have : (FormalCoproduct.evalOp.{u} X.Opens (ModuleCat.{u} R)).Additive :=
    FormalCoproductEvaluationAdditive.formalCoproductEvalOp_additive
  dsimp only [orderedCoefficientCechObjectFunctor]
  infer_instance

private theorem orderedCoefficientCechCoface_naturality
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (n : ℕ) (k : Fin (n + 2)) :
    CoefficientCechTerms.orderedCoefficientCechCoface c M U n k ≫
        (orderedCoefficientCechObjectFunctor c U (n + 1)).map f =
      (orderedCoefficientCechObjectFunctor c U n).map f ≫
        CoefficientCechTerms.orderedCoefficientCechCoface c N U n k := by
  let E : (X.Opensᵒᵖ ⥤ ModuleCat.{u} R) ⥤
      ((FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤
        ModuleCat.{u} R) :=
    FormalCoproduct.evalOp X.Opens
      (ModuleCat.{u} R)
  let α := E.map ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).map f)
  exact α.naturality (SectionCechIndices.orderedCechFace U n k).op

private theorem orderedCoefficientCechDifferential_naturality
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    CoefficientCechComplex.orderedCoefficientCechDifferential c M U n ≫
        (orderedCoefficientCechObjectFunctor c U (n + 1)).map f =
      (orderedCoefficientCechObjectFunctor c U n).map f ≫
        CoefficientCechComplex.orderedCoefficientCechDifferential c N U n := by
  let fn : CoefficientCechTerms.orderedCoefficientCechObject c M U n ⟶
      CoefficientCechTerms.orderedCoefficientCechObject c N U n :=
    (orderedCoefficientCechObjectFunctor c U n).map f
  let fn1 : CoefficientCechTerms.orderedCoefficientCechObject c M U (n + 1) ⟶
      CoefficientCechTerms.orderedCoefficientCechObject c N U (n + 1) :=
    (orderedCoefficientCechObjectFunctor c U (n + 1)).map f
  change CoefficientCechComplex.orderedCoefficientCechDifferential c M U n ≫ fn1 =
    fn ≫ CoefficientCechComplex.orderedCoefficientCechDifferential c N U n
  have hface (k : Fin (n + 2)) :
      CoefficientCechTerms.orderedCoefficientCechCoface c M U n k ≫ fn1 =
        fn ≫ CoefficientCechTerms.orderedCoefficientCechCoface c N U n k :=
    orderedCoefficientCechCoface_naturality c f U n k
  have hterm (k : Fin (n + 2)) :
      ((-1 : ℤ) ^ (k : ℕ) • CoefficientCechTerms.orderedCoefficientCechCoface c M U n k) ≫ fn1 =
        fn ≫ ((-1 : ℤ) ^ (k : ℕ) •
          CoefficientCechTerms.orderedCoefficientCechCoface c N U n k) := by
    calc
      _ = (-1 : ℤ) ^ (k : ℕ) •
          (CoefficientCechTerms.orderedCoefficientCechCoface c M U n k ≫ fn1) :=
        Preadditive.zsmul_comp _ _ _
      _ = (-1 : ℤ) ^ (k : ℕ) •
          (fn ≫ CoefficientCechTerms.orderedCoefficientCechCoface c N U n k) :=
        congrArg (fun q ↦ (-1 : ℤ) ^ (k : ℕ) • q) (hface k)
      _ = _ := (Preadditive.comp_zsmul _ _ _).symm
  change
    (∑ k : Fin (n + 2),
        (-1 : ℤ) ^ (k : ℕ) • CoefficientCechTerms.orderedCoefficientCechCoface c M U n k) ≫ fn1 =
      fn ≫ ∑ k : Fin (n + 2),
        (-1 : ℤ) ^ (k : ℕ) • CoefficientCechTerms.orderedCoefficientCechCoface c N U n k
  calc
    _ = ∑ k : Fin (n + 2),
        ((-1 : ℤ) ^ (k : ℕ) • CoefficientCechTerms.orderedCoefficientCechCoface c M U n k) ≫ fn1 :=
      Preadditive.sum_comp Finset.univ _ _
    _ = ∑ k : Fin (n + 2),
        fn ≫ ((-1 : ℤ) ^ (k : ℕ) • CoefficientCechTerms.orderedCoefficientCechCoface c N U n k) :=
      Finset.sum_congr rfl fun k _ ↦ hterm k
    _ = _ := (Preadditive.comp_sum Finset.univ _ _).symm

private noncomputable def orderedCoefficientCechComplexMap
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    CoefficientCechComplex.orderedCoefficientCechComplex c M U ⟶ CoefficientCechComplex.orderedCoefficientCechComplex c N U :=
  CochainComplex.ofHom
    (fun n ↦ (orderedCoefficientCechObjectFunctor c U n).map f)
    (fun n ↦ by
      rw [CoefficientCechComplex.orderedCoefficientCechComplex_d, CoefficientCechComplex.orderedCoefficientCechComplex_d]
      exact (orderedCoefficientCechDifferential_naturality c f U n).symm)

/-- The ordered base-linear Cech complex, functorially in the scheme module. -/
noncomputable def orderedCoefficientCechComplexFunctor
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) :
    X.Modules ⥤ CochainComplex (ModuleCat.{u} R) ℕ where
  obj M := CoefficientCechComplex.orderedCoefficientCechComplex c M U
  map f := orderedCoefficientCechComplexMap c f U
  map_id M := by
    apply HomologicalComplex.Hom.ext
    funext n
    change (orderedCoefficientCechObjectFunctor c U n).map (𝟙 M) = 𝟙 _
    exact (orderedCoefficientCechObjectFunctor c U n).map_id M
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    change (orderedCoefficientCechObjectFunctor c U n).map (f ≫ g) =
      (orderedCoefficientCechObjectFunctor c U n).map f ≫
        (orderedCoefficientCechObjectFunctor c U n).map g
    exact (orderedCoefficientCechObjectFunctor c U n).map_comp f g

@[simp]
theorem orderedCoefficientCechComplexFunctor_obj
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (M : X.Modules) :
    (orderedCoefficientCechComplexFunctor c U).obj M =
      CoefficientCechComplex.orderedCoefficientCechComplex c M U :=
  rfl

instance orderedCoefficientCechComplexFunctor_additive
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) :
    (orderedCoefficientCechComplexFunctor c U).Additive where
  map_add := by
    intro M N f g
    apply HomologicalComplex.Hom.ext
    funext n
    change (orderedCoefficientCechObjectFunctor c U n).map (f + g) =
      (orderedCoefficientCechObjectFunctor c U n).map f +
        (orderedCoefficientCechObjectFunctor c U n).map g
    exact Functor.map_add _

instance orderedCoefficientCechComplexFunctor_preservesZeroMorphisms
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) :
    (orderedCoefficientCechComplexFunctor c U).PreservesZeroMorphisms where
  map_zero M N := by
    apply HomologicalComplex.Hom.ext
    funext n
    change Limits.Pi.map (fun _ ↦ 0) = 0
    refine Pi.hom_ext _ _ fun i ↦ ?_
    rw [Pi.map_π, comp_zero]
    exact CategoryTheory.Limits.zero_comp.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechFunctor
