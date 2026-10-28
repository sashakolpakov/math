/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
This file has been modified.
-/
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import OAI.AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic
import OAI.AlgebraicGeometry.SheafCohomology.Projective.AffineSectionExact
import OAI.AlgebraicGeometry.SheafCohomology.Module
import OAI.AlgebraicGeometry.SheafCohomology.Cech.Cochains

/-! # Base Cech Exact -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechExact.Scheme.Modules

noncomputable section

open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules

/-

ForMathlib (OURS, not vendored): upstream candidate.
-/

/-!
# Exact sequences of base-linear Cech complexes

This file proves that a short exact sequence of quasicoherent scheme modules remains short exact
after taking base-linear sections over an affine open. The finite affine Cech-complex consequence
is assembled degreewise below.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

universe u

/-- A short exact sequence of quasicoherent scheme modules remains short exact after taking
base-linear sections over an affine open. -/
theorem _root_.OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechExact.CategoryTheory.ShortComplex.ShortExact.map_baseModulePresheafFunctor_eval_of_isAffineOpen
    {X S : Scheme.{u}} (π : X ⟶ S)
    {T : ShortComplex X.Modules} (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    (T.map (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π ⋙
      (CategoryTheory.evaluation X.Opensᵒᵖ
        (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))).obj (op U))).ShortExact := by
  let A := T.map (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π ⋙
    (CategoryTheory.evaluation X.Opensᵒᵖ
      (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))).obj (op U))
  let K := T.map (Module.ProjectiveAffine.ModuleSheaf.toSheaf X)
  have hK : K.ShortExact := hT.map_of_exact (Module.ProjectiveAffine.ModuleSheaf.toSheaf X)
  have : Mono T.f := hT.mono_f
  have : Epi T.g := hT.epi_g
  have : Mono A.f := by
    rw [ModuleCat.mono_iff_injective]
    change Function.Injective (K.f.hom.app (op U)).hom
    have : Mono K.f := hK.mono_f
    have : Mono K.f.hom := by
      change Mono ((CategoryTheory.sheafToPresheaf
        (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map K.f)
      infer_instance
    have : Mono (K.f.hom.app (op U)) := by infer_instance
    exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  have : Epi A.g := by
    rw [ModuleCat.epi_iff_surjective]
    exact AffineSectionExact.affineSections_surjective_of_shortExact hT U hU
  refine ShortComplex.ShortExact.mk ?_
  change A.Exact
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  have hy' : K.g.hom.app (op U) y = 0 := hy
  obtain ⟨x, hx⟩ := TopCat.Sheaf.sections_exact_of_left_exact
    (U := U) hK.exact hK.mono_f y hy'
  exact ⟨x, hx⟩

private noncomputable def baseCechFunctorXIsoPi
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U).obj M).X n ≅
      ModuleCat.of Γ(S, (⊤ : S.Opens))
        (∀ i : Fin (n + 1) → ι,
          ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).obj M).obj
            (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i k)))) :=
  ModuleCat.piIsoPi _

@[simp]
private theorem baseCechFunctorXIsoPi_hom_apply
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (x : ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U).obj M).X n)
    (i : Fin (n + 1) → ι) :
    (baseCechFunctorXIsoPi π M U n).hom x i =
      Pi.π (fun j : Fin (n + 1) → ι ↦
        ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).obj M).obj
          (op (∏ᶜ fun k : Fin (n + 1) ↦ U (j k)))) i x :=
  ModuleCat.piIsoPi_hom_ker_subtype_apply _ i x

private theorem baseCechFunctorXIsoPi_hom_map_apply
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (x : ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U).obj M).X n)
    (i : Fin (n + 1) → ι) :
    (baseCechFunctorXIsoPi π N U n).hom
        (((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U).map f).f n x) i =
      (((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map f).app
        (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i k))))
        ((baseCechFunctorXIsoPi π M U n).hom x i) := by
  rw [baseCechFunctorXIsoPi_hom_apply,
    baseCechFunctorXIsoPi_hom_apply]
  exact ConcreteCategory.congr_hom
    (Limits.Pi.map_π (fun j : Fin (n + 1) → ι ↦
      ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map f).app
        (op (∏ᶜ fun k : Fin (n + 1) ↦ U (j k)))) i) x

/-- A short exact sequence of quasicoherent scheme modules remains short exact after taking its
base-linear Cech complexes on a finite affine family. -/
theorem _root_.OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechExact.CategoryTheory.ShortComplex.ShortExact.map_baseCechComplexFunctor_of_affine_openCover
    {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i))
    {T : ShortComplex X.Modules} (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent] :
    (T.map (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let A := (T.map (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U)).map
    (HomologicalComplex.eval _ _ n)
  change A.ShortExact
  have hlocal (i : Fin (n + 1) → ι) :=
    BaseCechExact.CategoryTheory.ShortComplex.ShortExact.map_baseModulePresheafFunctor_eval_of_isAffineOpen
      π hT (∏ᶜ fun k : Fin (n + 1) ↦ U (i k))
      (Cech.Cochains.IsAffineOpen.cechIntersection U hU n i)
  have : Mono A.f := by
    rw [ModuleCat.mono_iff_injective]
    change Function.Injective (((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U).map T.f).f n)
    intro x y hxy
    apply (ModuleCat.mono_iff_injective
      (baseCechFunctorXIsoPi π T.X₁ U n).hom).mp inferInstance
    funext i
    have hi := congrArg
      (fun z ↦ (baseCechFunctorXIsoPi π T.X₂ U n).hom z i) hxy
    rw [baseCechFunctorXIsoPi_hom_map_apply,
      baseCechFunctorXIsoPi_hom_map_apply] at hi
    exact (hlocal i).moduleCat_injective_f hi
  have : Epi A.g := by
    rw [ModuleCat.epi_iff_surjective]
    change Function.Surjective (((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U).map T.g).f n)
    intro y
    have preimage (i : Fin (n + 1) → ι) :
        ∃ x : ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).obj T.X₂).obj
            (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i k))),
          ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map T.g).app
              (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i k))) x =
            (baseCechFunctorXIsoPi π T.X₃ U n).hom y i :=
      (hlocal i).moduleCat_surjective_g _
    choose x hx using preimage
    let x' := (baseCechFunctorXIsoPi π T.X₂ U n).inv x
    refine ⟨x', ?_⟩
    apply (ModuleCat.mono_iff_injective
      (baseCechFunctorXIsoPi π T.X₃ U n).hom).mp inferInstance
    funext i
    rw [baseCechFunctorXIsoPi_hom_map_apply]
    have hx'i : (baseCechFunctorXIsoPi π T.X₂ U n).hom x' i = x i :=
      congrFun (Iso.inv_hom_id_apply
        (baseCechFunctorXIsoPi π T.X₂ U n) x) i
    rw [hx'i]
    exact hx i
  refine ShortComplex.ShortExact.mk ?_
  change ((T.map (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U)).map
    (HomologicalComplex.eval _ _ n)).Exact
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  change ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U).obj T.X₂).X n at y
  change (((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U).map T.g).f n) y = 0 at hy
  have preimage (i : Fin (n + 1) → ι) :
      ∃ x : ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).obj T.X₁).obj
          (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i k))),
        ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map T.f).app
            (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i k))) x =
          (baseCechFunctorXIsoPi π T.X₂ U n).hom y i := by
    have hyi :
        ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map T.g).app
            (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i k)))
              ((baseCechFunctorXIsoPi π T.X₂ U n).hom y i) = 0 := by
      calc
        _ = (baseCechFunctorXIsoPi π T.X₃ U n).hom
            (((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U).map T.g).f n y) i :=
          (baseCechFunctorXIsoPi_hom_map_apply π T.g U n y i).symm
        _ = 0 := by rw [hy, map_zero]; rfl
    exact ((ShortComplex.moduleCat_exact_iff _).mp (hlocal i).exact) _ hyi
  choose x hx using preimage
  let x' := (baseCechFunctorXIsoPi π T.X₁ U n).inv x
  refine ⟨x', ?_⟩
  change (((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U).map T.f).f n) x' = y
  apply (ModuleCat.mono_iff_injective
    (baseCechFunctorXIsoPi π T.X₂ U n).hom).mp inferInstance
  funext i
  rw [baseCechFunctorXIsoPi_hom_map_apply]
  have hx'i : (baseCechFunctorXIsoPi π T.X₁ U n).hom x' i = x i :=
    congrFun (Iso.inv_hom_id_apply
      (baseCechFunctorXIsoPi π T.X₁ U n) x) i
  rw [hx'i]
  exact hx i

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechExact.Scheme.Modules
