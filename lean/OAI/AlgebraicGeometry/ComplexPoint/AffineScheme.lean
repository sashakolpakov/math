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
import OAI.AlgebraicGeometry.ComplexPoint.BasicNe
import OAI.AlgebraicGeometry.ComplexPoint.AffineSpace
import OAI.CategoryTheory.ConcreteCategory.Notation
import Mathlib.Logic.Equiv.PartialEquiv

/-! # Affine Scheme -/

namespace OAI.AlgebraicGeometry.ComplexPoint

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Complex points of affine schemes

The complex points of `Spec R` are canonically homeomorphic to the space of complex algebra
homomorphisms from `R` to `ℂ`, equipped with the topology of pointwise convergence. The proof of
continuity in the reverse direction uses the localization description of regular functions on
principal opens.
-/

open _root_.CategoryTheory _root_.Topology

variable (R : Type) [CommRing R] [Algebra ℂ R]

/-- The topology of pointwise convergence on complex algebra homomorphisms. -/
noncomputable instance Basic.ComplexSchemePoint.affineAlgebraHomTopology : TopologicalSpace (R →ₐ[ℂ] ℂ) :=
  TopologicalSpace.induced (fun φ : R →ₐ[ℂ] ℂ ↦ (φ : R → ℂ)) inferInstance

/-- The structure morphism of an affine complex scheme. -/
abbrev Basic.ComplexSchemePoint.affineSpecStructureMap : Spec ↧R ⟶ Spec ↧ℂ :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ R))

/-- Complex points of `Spec R` correspond to complex algebra homomorphisms from `R` to `ℂ`. -/
def Basic.ComplexSchemePoint.affineSpecEquiv :
    Basic.ComplexSchemePoint (Over.mk (Basic.ComplexSchemePoint.affineSpecStructureMap R)) ≃ (R →ₐ[ℂ] ℂ) where
  toFun z :=
    { toRingHom := (Spec.homEquiv z.left).hom
      commutes' c := by
        have hz := congrArg Spec.preimage (Over.w z)
        have hr : CommRingCat.ofHom (algebraMap ℂ R) ≫ Spec.preimage z.left =
            𝟙 (CommRingCat.of ℂ) := by
          simpa [Basic.ComplexSchemePoint.affineSpecStructureMap, Spec.preimage_comp] using hz
        exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hr) c }
  invFun φ := Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ R)) = 𝟙 (Spec ↧ℂ)
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext c
    exact φ.commutes c)
  left_inv z := Over.OverMorphism.ext (Spec.map_preimage z.left)
  right_inv φ := by
    ext r
    simp [Spec.homEquiv_apply]

lemma Basic.ComplexSchemePoint.affineSpecEquiv_apply
    (z : Basic.ComplexSchemePoint (Over.mk (Basic.ComplexSchemePoint.affineSpecStructureMap R))) (r : R) :
    Basic.ComplexSchemePoint.affineSpecEquiv R z r =
      Basic.Point.evaluate ⊤ ((Scheme.ΓSpecIso ↧R).inv r) z := by
  rw [Basic.ComplexSchemePoint.evaluate_top_eq_appTop]
  change (Spec.preimage z.left).hom r =
    (Scheme.ΓSpecIso ↧ℂ).hom (z.left.appTop ((Scheme.ΓSpecIso ↧R).inv r))
  have h := Scheme.ΓSpecIso_naturality (Spec.preimage z.left)
  have h' := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h)
    ((Scheme.ΓSpecIso ↧R).inv r)
  simpa using h'.symm

lemma Basic.ComplexSchemePoint.evaluate_affineSpecEquiv_symm_top (s : Γ(Spec ↧R, ⊤)) (φ : R →ₐ[ℂ] ℂ) :
    Basic.Point.evaluate ⊤ s ((Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ) =
      φ ((Scheme.ΓSpecIso ↧R).hom s) := by
  calc
    Basic.Point.evaluate ⊤ s ((Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ) =
        Basic.Point.evaluate ⊤ ((Scheme.ΓSpecIso ↧R).inv
          ((Scheme.ΓSpecIso ↧R).hom s)) ((Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ) := by simp
    _ = Basic.ComplexSchemePoint.affineSpecEquiv R ((Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ)
          ((Scheme.ΓSpecIso ↧R).hom s) :=
      (Basic.ComplexSchemePoint.affineSpecEquiv_apply R _ _).symm
    _ = φ ((Scheme.ΓSpecIso ↧R).hom s) := by simp

lemma Basic.ComplexSchemePoint.continuous_affineAlgebraHom_apply (r : R) :
    Continuous (fun φ : R →ₐ[ℂ] ℂ ↦ φ r) :=
  (continuous_apply r).comp continuous_induced_dom

lemma Basic.ComplexSchemePoint.continuous_affineSpecEquiv :
    @Continuous
      (Basic.ComplexSchemePoint (Over.mk (Basic.ComplexSchemePoint.affineSpecStructureMap R)))
      (R →ₐ[ℂ] ℂ) Basic.Point.analyticTopology (Basic.ComplexSchemePoint.affineAlgebraHomTopology R)
      (Basic.ComplexSchemePoint.affineSpecEquiv R) := by
  rw [continuous_induced_rng]
  exact continuous_pi fun r ↦ by
    simpa only [Function.comp_apply, Basic.ComplexSchemePoint.affineSpecEquiv_apply] using
      Basic.ComplexSchemePoint.continuous_evaluate_top (X := Over.mk (Basic.ComplexSchemePoint.affineSpecStructureMap R))
        ((Scheme.ΓSpecIso ↧R).inv r)

lemma Basic.ComplexSchemePoint.isOpen_affineSpecEquiv_symm_preimage_overOpen_basicOpen
    (s : Γ(Spec ↧R, ⊤)) :
    IsOpen ((Basic.ComplexSchemePoint.affineSpecEquiv R).symm ⁻¹'
      Basic.Point.overOpen ((Spec ↧R).basicOpen s)) := by
  rw [show (Basic.ComplexSchemePoint.affineSpecEquiv R).symm ⁻¹'
      Basic.Point.overOpen ((Spec ↧R).basicOpen s) =
      {φ | φ ((Scheme.ΓSpecIso ↧R).hom s) ≠ 0} by
    ext φ
    exact (Basic.Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
      (X := Over.mk (Basic.ComplexSchemePoint.affineSpecStructureMap R)) (U := ⊤)
      s ((Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ) trivial).trans
        (Iff.of_eq (congrArg (· ≠ 0) (Basic.ComplexSchemePoint.evaluate_affineSpecEquiv_symm_top R s φ)))]
  exact isOpen_ne_fun
    (Basic.ComplexSchemePoint.continuous_affineAlgebraHom_apply R ((Scheme.ΓSpecIso ↧R).hom s))
    continuous_const

/-- On an affine scheme, evaluation of a section on a principal open is locally a quotient of
evaluations of global sections. -/
lemma Basic.ComplexSchemePoint.exists_evaluate_affine_basicOpen_eq_div {X : Over (Spec ↧ℂ)} [IsAffine X.left]
    (f : Γ(X.left, ⊤)) (t : Γ(X.left, X.left.basicOpen f)) :
    ∃ (k : ℕ) (a : Γ(X.left, ⊤)),
      ∀ z : Basic.ComplexSchemePoint X, z ∈ Basic.Point.overOpen (X.left.basicOpen f) →
        Basic.Point.evaluate (X.left.basicOpen f) t z = Basic.Point.evaluate ⊤ a z / Basic.Point.evaluate ⊤ f z ^ k :=
  Basic.Point.exists_evaluate_basicOpen_eq_div (X := X) (isAffineOpen_top X.left) f t

lemma Basic.ComplexSchemePoint.exists_evaluate_affineSpec_basicOpen_eq_div
    (f : Γ(Spec ↧R, ⊤))
    (t : Γ(Spec ↧R, (Spec ↧R).basicOpen f)) :
    ∃ (k : ℕ) (a : Γ(Spec ↧R, ⊤)),
      ∀ z : Basic.ComplexSchemePoint (Over.mk (Basic.ComplexSchemePoint.affineSpecStructureMap R)),
        z ∈ Basic.Point.overOpen ((Spec ↧R).basicOpen f) →
          Basic.Point.evaluate ((Spec ↧R).basicOpen f) t z =
            Basic.Point.evaluate ⊤ a z / Basic.Point.evaluate ⊤ f z ^ k := by
  let : IsAffine (Over.mk (Basic.ComplexSchemePoint.affineSpecStructureMap R)).left :=
    inferInstanceAs (IsAffine (Spec ↧R))
  exact Basic.ComplexSchemePoint.exists_evaluate_affine_basicOpen_eq_div (X := Over.mk (Basic.ComplexSchemePoint.affineSpecStructureMap R)) f t

lemma Basic.ComplexSchemePoint.continuousOn_evaluate_affineSpec_basicOpen_equiv_symm
    (f : Γ(Spec ↧R, ⊤))
    (t : Γ(Spec ↧R, (Spec ↧R).basicOpen f)) :
    ContinuousOn
      (fun φ : R →ₐ[ℂ] ℂ ↦ Basic.Point.evaluate ((Spec ↧R).basicOpen f) t
        ((Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ))
      ((Basic.ComplexSchemePoint.affineSpecEquiv R).symm ⁻¹'
        Basic.Point.overOpen ((Spec ↧R).basicOpen f)) := by
  obtain ⟨k, a, h⟩ := Basic.ComplexSchemePoint.exists_evaluate_affineSpec_basicOpen_eq_div R f t
  have ha : Continuous (fun φ : R →ₐ[ℂ] ℂ ↦
      Basic.Point.evaluate ⊤ a ((Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ)) := by
    simpa only [Basic.ComplexSchemePoint.evaluate_affineSpecEquiv_symm_top] using
      Basic.ComplexSchemePoint.continuous_affineAlgebraHom_apply R ((Scheme.ΓSpecIso ↧R).hom a)
  have hf : Continuous (fun φ : R →ₐ[ℂ] ℂ ↦
      Basic.Point.evaluate ⊤ f ((Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ)) := by
    simpa only [Basic.ComplexSchemePoint.evaluate_affineSpecEquiv_symm_top] using
      Basic.ComplexSchemePoint.continuous_affineAlgebraHom_apply R ((Scheme.ΓSpecIso ↧R).hom f)
  have hrat : ContinuousOn
      (fun φ : R →ₐ[ℂ] ℂ ↦ Basic.Point.evaluate ⊤ a ((Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ) /
        Basic.Point.evaluate ⊤ f ((Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ) ^ k)
      ((Basic.ComplexSchemePoint.affineSpecEquiv R).symm ⁻¹'
        Basic.Point.overOpen ((Spec ↧R).basicOpen f)) :=
    ha.continuousOn.div (hf.pow k).continuousOn fun φ hφ ↦
      pow_ne_zero k ((Basic.Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
        (X := Over.mk (Basic.ComplexSchemePoint.affineSpecStructureMap R)) (U := ⊤) f _ trivial).mp hφ)
  exact hrat.congr fun φ hφ ↦ h _ hφ

lemma Basic.ComplexSchemePoint.continuous_affineSpecEquiv_symm :
    @Continuous (R →ₐ[ℂ] ℂ)
      (Basic.ComplexSchemePoint (Over.mk (Basic.ComplexSchemePoint.affineSpecStructureMap R)))
      (Basic.ComplexSchemePoint.affineAlgebraHomTopology R) Basic.Point.analyticTopology (Basic.ComplexSchemePoint.affineSpecEquiv R).symm := by
  rw [Basic.Point.continuous_iff_analyticSubbasis]
  rintro W ⟨U, s, V, hV, rfl⟩
  apply isOpen_iff_forall_mem_open.mpr
  rintro φ ⟨hφU, hφV⟩
  obtain ⟨f, hfU, hφf⟩ :=
    (isAffineOpen_top (Spec ↧R)).exists_basicOpen_le
      ⟨((Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ).underlying, hφU⟩ trivial
  let t := (Spec ↧R).presheaf.map (homOfLE hfU).op s
  let N := (Basic.ComplexSchemePoint.affineSpecEquiv R).symm ⁻¹'
      Basic.Point.overOpen ((Spec ↧R).basicOpen f) ∩
    (fun ψ : R →ₐ[ℂ] ℂ ↦ Basic.Point.evaluate ((Spec ↧R).basicOpen f) t
      ((Basic.ComplexSchemePoint.affineSpecEquiv R).symm ψ)) ⁻¹' V
  have hNopen : IsOpen N :=
    (Basic.ComplexSchemePoint.continuousOn_evaluate_affineSpec_basicOpen_equiv_symm R f t).isOpen_inter_preimage
      (Basic.ComplexSchemePoint.isOpen_affineSpecEquiv_symm_preimage_overOpen_basicOpen R f) hV
  refine ⟨N, ?_, hNopen, ?_⟩
  · rintro ψ ⟨hψf, hψV⟩
    have hψU : (Basic.ComplexSchemePoint.affineSpecEquiv R).symm ψ ∈ Basic.Point.overOpen U := hfU hψf
    refine ⟨hψU, ?_⟩
    change Basic.Point.evaluate U s ((Basic.ComplexSchemePoint.affineSpecEquiv R).symm ψ) ∈ V
    rwa [Basic.Point.evaluate_res hfU s _ hψf]
  · refine ⟨hφf, ?_⟩
    change Basic.Point.evaluate ((Spec ↧R).basicOpen f) t
      ((Basic.ComplexSchemePoint.affineSpecEquiv R).symm φ) ∈ V
    exact (congrArg (fun c ↦ c ∈ V) (Basic.Point.evaluate_res hfU s _ hφf)).mp hφV

/-- The complex points of `Spec R` are homeomorphic to the complex algebra homomorphisms
from `R` to `ℂ`, with their topology of pointwise convergence. -/
def Basic.ComplexSchemePoint.affineSpecHomeomorph :
    @Homeomorph
      (Basic.ComplexSchemePoint (Over.mk (Basic.ComplexSchemePoint.affineSpecStructureMap R)))
      (R →ₐ[ℂ] ℂ) Basic.Point.analyticTopology (Basic.ComplexSchemePoint.affineAlgebraHomTopology R) where
  toEquiv := Basic.ComplexSchemePoint.affineSpecEquiv R
  continuous_toFun := Basic.ComplexSchemePoint.continuous_affineSpecEquiv R
  continuous_invFun := Basic.ComplexSchemePoint.continuous_affineSpecEquiv_symm R

variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

lemma Basic.ComplexSchemePoint.specMap_comp_affineSpecStructureMap (g : A →ₐ[ℂ] B) :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Basic.ComplexSchemePoint.affineSpecStructureMap A =
      Basic.ComplexSchemePoint.affineSpecStructureMap B := by
  rw [← Spec.map_comp]
  congr 1
  ext c
  exact g.commutes c

/-- The map on complex points contravariantly associated to a complex algebra homomorphism. -/
def Basic.ComplexSchemePoint.affineSpecComplexPointMap (g : A →ₐ[ℂ] B) :
    Basic.ComplexSchemePoint (Over.mk (Basic.ComplexSchemePoint.affineSpecStructureMap B)) →
      Basic.ComplexSchemePoint (Over.mk (Basic.ComplexSchemePoint.affineSpecStructureMap A)) :=
  Basic.Point.map (Over.homMk (Spec.map (CommRingCat.ofHom g.toRingHom))
    (Basic.ComplexSchemePoint.specMap_comp_affineSpecStructureMap g))

/-- Under the affine-point equivalence, an affine scheme map acts by precomposition of algebra
homomorphisms. -/
lemma Basic.ComplexSchemePoint.affineSpecEquiv_affineSpecComplexPointMap (g : A →ₐ[ℂ] B)
    (z : Basic.ComplexSchemePoint (Over.mk (Basic.ComplexSchemePoint.affineSpecStructureMap B))) :
    Basic.ComplexSchemePoint.affineSpecEquiv A (Basic.ComplexSchemePoint.affineSpecComplexPointMap g z) =
      (Basic.ComplexSchemePoint.affineSpecEquiv B z).comp g := by
  ext a
  simp [Basic.ComplexSchemePoint.affineSpecComplexPointMap, Basic.Point.map, Basic.ComplexSchemePoint.affineSpecEquiv, Spec.preimage_comp]

end

end OAI.AlgebraicGeometry.ComplexPoint
