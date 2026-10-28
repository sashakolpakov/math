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
import OAI.Algebra.Homology.LinearDualHomotopy

/-! # Linear Dual Naturality -/

namespace OAI.Algebra.Homology.LinearDualNaturality

noncomputable section

open _root_.CategoryTheory
open _root_.CategoryTheory.ShortComplex
open _root_.HomologicalComplex

/-!
# Naturality of linear duality on homology

Concrete cycle representatives and the canonical universal-coefficient equivalence are
compatible with morphisms of short complexes. These identities are used to descend
geometric cap-product identities in the cohomology variable.

The same holds one level up: the universal-coefficient equivalence
`HomologicalComplex.linearDualHomologyEquiv` between the cohomology of the linear-dual cochain
complex and the dual of homology intertwines the dualised cochain map with the dual of the
homology map.
-/

universe u

namespace CategoryTheory.ShortComplex

section CommRing
variable {R : Type u} [CommRing R]

/-- The canonical class of an explicit cycle in a short complex of modules. -/
def moduleCatHomologyClass (S : ShortComplex (ModuleCat.{u} R)) :
    LinearMap.ker S.g.hom →ₗ[R] S.homology :=
  S.moduleCatHomologyIso.inv.hom.comp (LinearMap.range S.moduleCatToCycles).mkQ

/-- Every homology class has an explicit cycle representative. -/
lemma moduleCatHomologyClass_surjective (S : ShortComplex (ModuleCat.{u} R)) :
    Function.Surjective (moduleCatHomologyClass S) :=
  S.moduleCatHomologyIso.toLinearEquiv.symm.surjective.comp
    (Submodule.mkQ_surjective _)

set_option backward.isDefEq.respectTransparency false in
/-- A morphism of short complexes sends cycles to cycles. -/
def moduleCatCycleMap {S T : ShortComplex (ModuleCat.{u} R)} (f : S ⟶ T) :
    LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom :=
  f.τ₂.hom.restrict (fun x hx ↦ by
    change T.g.hom (f.τ₂.hom x) = 0
    have h := ConcreteCategory.congr_hom f.comm₂₃ x
    change T.g.hom (f.τ₂.hom x) = f.τ₃.hom (S.g.hom x) at h
    rwa [show S.g.hom x = 0 from hx, map_zero] at h)

set_option backward.isDefEq.respectTransparency false in
lemma moduleCatCyclesIso_inv_cycleMap {S T : ShortComplex (ModuleCat.{u} R)}
    (f : S ⟶ T) :
    S.moduleCatCyclesIso.inv ≫ cyclesMap f =
      ModuleCat.ofHom (moduleCatCycleMap f) ≫ T.moduleCatCyclesIso.inv := by
  rw [← cancel_mono T.iCycles]
  simp only [Category.assoc, ShortComplex.cyclesMap_i, moduleCatCyclesIso_inv_iCycles_assoc,
    moduleCatCyclesIso_inv_iCycles]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Taking the class of a cycle commutes with the induced homology map. -/
lemma moduleCatHomologyClass_naturality {S T : ShortComplex (ModuleCat.{u} R)}
    (f : S ⟶ T) (x : LinearMap.ker S.g.hom) :
    (homologyMap f).hom ((moduleCatHomologyClass S) x) =
      (moduleCatHomologyClass T) (moduleCatCycleMap f x) := by
  have h :
      S.moduleCatCyclesIso.inv ≫ S.homologyπ ≫ homologyMap f =
        ModuleCat.ofHom (moduleCatCycleMap f) ≫ T.moduleCatCyclesIso.inv ≫ T.homologyπ := by
    rw [ShortComplex.homologyπ_naturality, ← Category.assoc, moduleCatCyclesIso_inv_cycleMap,
      Category.assoc]
  exact ConcreteCategory.congr_hom h x

set_option backward.isDefEq.respectTransparency false in
/-- Reversed linear-dual short complexes are contravariantly functorial. -/
def linearDualMap {S T : ShortComplex (ModuleCat.{u} R)} (f : S ⟶ T) :
    (LinearDual.CategoryTheory.ShortComplex.linearDual T) ⟶ (LinearDual.CategoryTheory.ShortComplex.linearDual S) where
  τ₁ := ModuleCat.ofHom f.τ₃.hom.dualMap
  τ₂ := ModuleCat.ofHom f.τ₂.hom.dualMap
  τ₃ := ModuleCat.ofHom f.τ₁.hom.dualMap
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    change Module.Dual R T.X₃ at phi
    apply LinearMap.ext
    intro x
    exact congrArg phi (ConcreteCategory.congr_hom f.comm₂₃ x).symm
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    change Module.Dual R T.X₂ at phi
    apply LinearMap.ext
    intro x
    exact congrArg phi (ConcreteCategory.congr_hom f.comm₁₂ x).symm

end CommRing

variable {R : Type u} [Field R]

set_option backward.isDefEq.respectTransparency false in
/-- Universal coefficients evaluate a dual cycle on an ordinary cycle without any
choice of generators or representatives in the resulting pairing. -/
lemma linearDualHomologyEquiv_class_apply_class (S : ShortComplex (ModuleCat.{u} R))
    (phi : LinearMap.ker S.f.hom.dualMap) (x : LinearMap.ker S.g.hom) :
    (LinearDual.CategoryTheory.ShortComplex.linearDualHomologyEquiv S) ((moduleCatHomologyClass (LinearDual.CategoryTheory.ShortComplex.linearDual S)) phi)
        ((moduleCatHomologyClass S) x) = (phi.1 : Module.Dual R S.X₂) x.1 := by
  change (LinearDual.CategoryTheory.ShortComplex.dualHomologyComparisonExplicit S)
      ((LinearDual.CategoryTheory.ShortComplex.linearDual S).moduleCatHomologyIso.hom.hom
        ((LinearDual.CategoryTheory.ShortComplex.linearDual S).moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi)))
      (S.moduleCatHomologyIso.hom.hom
        (S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk x))) =
      (phi.1 : Module.Dual R S.X₂) x.1
  have hphi := ConcreteCategory.congr_hom
    (LinearDual.CategoryTheory.ShortComplex.linearDual S).moduleCatHomologyIso.inv_hom_id (Submodule.Quotient.mk phi)
  have hx := ConcreteCategory.congr_hom
    S.moduleCatHomologyIso.inv_hom_id (Submodule.Quotient.mk x)
  change (LinearDual.CategoryTheory.ShortComplex.linearDual S).moduleCatHomologyIso.hom.hom
    ((LinearDual.CategoryTheory.ShortComplex.linearDual S).moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi)) =
      Submodule.Quotient.mk phi at hphi
  change S.moduleCatHomologyIso.hom.hom
    (S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk x at hx
  rw [hphi, hx]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The universal-coefficient equivalence is natural in the complex. -/
theorem linearDualHomologyEquiv_naturality
    {S T : ShortComplex (ModuleCat.{u} R)} (f : S ⟶ T)
    (alpha : (LinearDual.CategoryTheory.ShortComplex.linearDual T).homology) :
    (LinearDual.CategoryTheory.ShortComplex.linearDualHomologyEquiv S) ((homologyMap (linearDualMap f)).hom alpha) =
      (homologyMap f).hom.dualMap ((LinearDual.CategoryTheory.ShortComplex.linearDualHomologyEquiv T) alpha) := by
  obtain ⟨phi, rfl⟩ := (moduleCatHomologyClass_surjective (LinearDual.CategoryTheory.ShortComplex.linearDual T)) alpha
  apply LinearMap.ext
  intro c
  obtain ⟨x, rfl⟩ := (moduleCatHomologyClass_surjective S) c
  change (LinearDual.CategoryTheory.ShortComplex.linearDualHomologyEquiv S)
      ((homologyMap (linearDualMap f)).hom ((moduleCatHomologyClass (LinearDual.CategoryTheory.ShortComplex.linearDual T)) phi))
      ((moduleCatHomologyClass S) x) =
    (LinearDual.CategoryTheory.ShortComplex.linearDualHomologyEquiv T) ((moduleCatHomologyClass (LinearDual.CategoryTheory.ShortComplex.linearDual T)) phi)
      ((homologyMap f).hom ((moduleCatHomologyClass S) x))
  rw [moduleCatHomologyClass_naturality, moduleCatHomologyClass_naturality,
    linearDualHomologyEquiv_class_apply_class, linearDualHomologyEquiv_class_apply_class]
  rfl

end CategoryTheory.ShortComplex

namespace HomologicalComplex

section CommRing
variable {R : Type u} [CommRing R]
  {K L : ChainComplex (ModuleCat.{u} R) ℕ}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The degreewise short-complex dual identification preserves maps. -/
lemma linearDualCochainComplexScIso_naturality (f : K ⟶ L) (n : ℕ) :
    (shortComplexFunctor (ModuleCat R) (.up ℕ) n).map (LinearDual.HomologicalComplex.linearDualMap f) ≫
      (LinearDual.HomologicalComplex.linearDualCochainComplexScIso K n).hom =
    (LinearDual.HomologicalComplex.linearDualCochainComplexScIso L n).hom ≫
      CategoryTheory.ShortComplex.linearDualMap ((shortComplexFunctor (ModuleCat R) (.down ℕ) n).map f) := rfl

end CommRing

variable {R : Type u} [Field R]
  {K L : ChainComplex (ModuleCat.{u} R) ℕ}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The universal-coefficient identification intertwines the dual
cochain map with the dual of the homology map. -/
lemma linearDualHomologyEquiv_naturality (f : K ⟶ L) (n : ℕ)
    (a : (LinearDual.HomologicalComplex.linearDualCochainComplex L).homology n) (z : K.homology n) :
    LinearDual.HomologicalComplex.linearDualHomologyEquiv K n (homologyMap (LinearDual.HomologicalComplex.linearDualMap f) n a) z =
      LinearDual.HomologicalComplex.linearDualHomologyEquiv L n a (homologyMap f n z) := by
  have h := congrArg (ShortComplex.homologyFunctor (ModuleCat R)).map
    (linearDualCochainComplexScIso_naturality f n)
  rw [Functor.map_comp, Functor.map_comp] at h
  have ha := ConcreteCategory.congr_hom h a
  change (LinearDual.CategoryTheory.ShortComplex.linearDualHomologyEquiv (K.sc n))
    (ShortComplex.homologyMap (LinearDual.HomologicalComplex.linearDualCochainComplexScIso K n).hom
      (homologyMap (LinearDual.HomologicalComplex.linearDualMap f) n a)) z = _
  rw [show ShortComplex.homologyMap (LinearDual.HomologicalComplex.linearDualCochainComplexScIso K n).hom
      (homologyMap (LinearDual.HomologicalComplex.linearDualMap f) n a) =
    ShortComplex.homologyMap
      (CategoryTheory.ShortComplex.linearDualMap ((shortComplexFunctor (ModuleCat R) (.down ℕ) n).map f))
      (ShortComplex.homologyMap (LinearDual.HomologicalComplex.linearDualCochainComplexScIso L n).hom a) from ha]
  exact congrArg (fun α => α z) (CategoryTheory.ShortComplex.linearDualHomologyEquiv_naturality _ _)

end HomologicalComplex

end

end OAI.Algebra.Homology.LinearDualNaturality
