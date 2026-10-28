import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SheafComplexLift
import OAI.AlgebraicTopology.Cohomology.Singular.StalkLocalIso
import Mathlib.Topology.Sheaves.Abelian

/-! # Local Stalk Quasi Iso -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalStalkQuasiIso.Constructions

noncomputable section

section

/-! Actual quasi-isomorphisms on arbitrarily small open neighborhoods induce stalk quasi-isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.TopCat.Presheaf
open OAI.AlgebraicTopology.Cohomology.Singular.StalkLocalIso

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R] {X : TopCat.{0}}
variable {K L : CochainComplex (X.Presheaf (ModuleCat.{0} R)) ℕ} (f : K ⟶ L)

theorem openCochainMap_homology_app_isIso (U : Opens X) (n : ℕ)
    [QuasiIsoAt (((AlgebraicTopology.Cohomology.Singular.Stalk.presheafSectionFunctor U).mapHomologicalComplex (ComplexShape.up ℕ)).map f) n] :
    IsIso ((HomologicalComplex.homologyMap f n).app (op U)) := by
  have : IsIso ((AlgebraicTopology.Cohomology.Singular.Stalk.openCohomologyIso K U n).hom ≫ (HomologicalComplex.homologyMap f n).app (op U)) := by
    rw [← AlgebraicTopology.Cohomology.Singular.Stalk.openCohomologyIso_naturality f U n]
    infer_instance
  exact IsIso.of_isIso_comp_left (AlgebraicTopology.Cohomology.Singular.Stalk.openCohomologyIso K U n).hom
    ((HomologicalComplex.homologyMap f n).app (op U))

theorem stalkCochainMap_quasiIso_of_locally (x : X)
    (hlocal : ∀ (U : Opens X), x∈U → ∃ (W : Opens X), x∈W ∧ W≤U ∧
      QuasiIso (((AlgebraicTopology.Cohomology.Singular.Stalk.presheafSectionFunctor W).mapHomologicalComplex (ComplexShape.up ℕ)).map f)) :
    QuasiIso (((stalkFunctor (ModuleCat.{0} R) x).mapHomologicalComplex (ComplexShape.up ℕ)).map f) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hs : IsIso ((stalkFunctor (ModuleCat.{0} R) x).map (HomologicalComplex.homologyMap f n)) := by
    apply AlgebraicTopology.Cohomology.Singular.StalkLocalIso.stalkMap_isIso_of_locally_isIso
    intro U hxU
    obtain ⟨W,hxW,hWU,hW⟩ := hlocal U hxU
    have := hW
    exact ⟨W,hxW,homOfLE hWU,openCochainMap_homology_app_isIso f W n⟩
  have : IsIso (HomologicalComplex.homologyMap
      (((stalkFunctor (ModuleCat.{0} R) x).mapHomologicalComplex (ComplexShape.up ℕ)).map f) n ≫
        (AlgebraicTopology.Cohomology.Singular.Stalk.stalkCohomologyIso L x n).hom) := by
    rw [AlgebraicTopology.Cohomology.Singular.Stalk.stalkCohomologyIso_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (AlgebraicTopology.Cohomology.Singular.Stalk.stalkCohomologyIso L x n).hom

variable {S : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ}

theorem sheafComplexLift_stalk_unit (g : K ⟶ AlgebraicTopology.Cohomology.Singular.SheafSections.sheafUnderlyingCochainComplex S) (x : X) :
    AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafificationStalkComplexHom K x ≫ AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainMap (SheafComplexLift.Constructions.sheafComplexLift g) x =
      ((stalkFunctor (ModuleCat.{0} R) x).mapHomologicalComplex (ComplexShape.up ℕ)).map g := by
  ext n : 1
  change (stalkFunctor (ModuleCat.{0} R) x).map (CategoryTheory.toSheafify
      (Opens.grothendieckTopology X) (K.X n)) ≫
    (stalkFunctor (ModuleCat.{0} R) x).map ((SheafComplexLift.Constructions.sheafComplexLift g).f n).hom =
      (stalkFunctor (ModuleCat.{0} R) x).map (g.f n)
  rw [← Functor.map_comp, SheafComplexLift.Constructions.sheafComplexLift_unit]

theorem sheafComplexLift_stalk_quasiIso_of_locally
    (g : K ⟶ AlgebraicTopology.Cohomology.Singular.SheafSections.sheafUnderlyingCochainComplex S) (x : X)
    (hlocal : ∀ (U : Opens X), x∈U → ∃ (W : Opens X), x∈W ∧ W≤U ∧
      QuasiIso (((AlgebraicTopology.Cohomology.Singular.Stalk.presheafSectionFunctor W).mapHomologicalComplex (ComplexShape.up ℕ)).map g)) :
    QuasiIso (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainMap (SheafComplexLift.Constructions.sheafComplexLift g) x) := by
  have := stalkCochainMap_quasiIso_of_locally g x hlocal
  have : QuasiIso (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafificationStalkComplexHom K x ≫ AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainMap (SheafComplexLift.Constructions.sheafComplexLift g) x) := by
    rw [sheafComplexLift_stalk_unit]
    infer_instance
  exact quasiIso_of_comp_left (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafificationStalkComplexHom K x)
    (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainMap (SheafComplexLift.Constructions.sheafComplexLift g) x)

end

/-! Canonical comparison of two genuine sheaf quotients from their actual stalk maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.TopCat.Presheaf
open ZeroObject

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R] {X : TopCat.{0}}
variable {A B C : TopCat.Sheaf (ModuleCat.{0} R) X}

abbrev moduleSheafStalk (x : X) :=
  TopCat.Sheaf.forget (ModuleCat.{0} R) X ⋙ stalkFunctor (ModuleCat.{0} R) x

theorem moduleSheafMorphism_eq_zero_of_stalk (f : A ⟶ B)
    (hf : ∀ x, (moduleSheafStalk x).map f = 0) : f=0 := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply section_ext B U.unop
  intro x hx
  change germ B.obj U.unop x hx ((f.hom.app U) s) = germ B.obj U.unop x hx 0
  rw [← stalkFunctor_map_germ_apply]
  have hx0 : (stalkFunctor (ModuleCat.{0} R) x).map f.hom = 0 := hf x
  rw [hx0, map_zero]
  rfl

theorem moduleSheaf_epi_of_stalk_epi (f : A ⟶ B)
    (hf : ∀ x, Epi ((moduleSheafStalk x).map f)) : Epi f := by
  let S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} R) X) :=
    ShortComplex.mk f (0 : B ⟶ 0) (by simp)
  apply (S.exact_iff_epi rfl).mp
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mpr
  intro x
  apply ((S.map (moduleSheafStalk x)).exact_iff_epi (by simp [S])).mpr
  exact hf x

theorem moduleSheaf_kernel_comp_eq_zero (f : A ⟶ B) (g : A ⟶ C)
    (h : ∀ x, IsIso ((moduleSheafStalk x).map f) ∨ IsZero ((moduleSheafStalk x).obj C)) :
    kernel.ι f ≫ g = 0 := by
  apply moduleSheafMorphism_eq_zero_of_stalk
  intro x
  rcases h x with hx | hx
  · have := hx
    have hk : (moduleSheafStalk x).map (kernel.ι f) = 0 := by
      apply (cancel_mono ((moduleSheafStalk x).map f)).mp
      rw [← Functor.map_comp, kernel.condition, Functor.map_zero, zero_comp]
    rw [Functor.map_comp, hk, zero_comp]
  · exact hx.eq_zero_of_tgt _

def epiQuotientComparisonIso {D : Type*} [Category D] [Abelian D]
    {A B C : D} (f : A ⟶ B) (g : A ⟶ C) [Epi f] [Epi g]
    (hfg : kernel.ι f ≫ g=0) (hgf : kernel.ι g ≫ f=0) : B ≅ C where
  hom := Abelian.epiDesc f g hfg
  inv := Abelian.epiDesc g f hgf
  hom_inv_id := by
    apply (cancel_epi f).mp
    rw [← Category.assoc, Abelian.comp_epiDesc, Abelian.comp_epiDesc, Category.comp_id]
  inv_hom_id := by
    apply (cancel_epi g).mp
    rw [← Category.assoc, Abelian.comp_epiDesc, Abelian.comp_epiDesc, Category.comp_id]

variable (f : A ⟶ B) (g : A ⟶ C)
variable (h : ∀ x, (IsIso ((moduleSheafStalk x).map f) ∧
    IsIso ((moduleSheafStalk x).map g)) ∨
  (IsZero ((moduleSheafStalk x).obj B) ∧ IsZero ((moduleSheafStalk x).obj C)))

include h

theorem moduleSheaf_localQuotient_epi : Epi f := by
  apply moduleSheaf_epi_of_stalk_epi
  intro x
  rcases h x with hx | hx
  · have := hx.1
    infer_instance
  · exact hx.1.epi _

def moduleSheafLocalQuotientIso : B ≅ C := by
  have := moduleSheaf_localQuotient_epi f g h
  have := moduleSheaf_localQuotient_epi g f (fun x => (h x).elim
    (fun hx => Or.inl hx.symm) (fun hx => Or.inr hx.symm))
  exact epiQuotientComparisonIso f g
    (moduleSheaf_kernel_comp_eq_zero f g (fun x => (h x).elim
      (fun hx => Or.inl hx.1) (fun hx => Or.inr hx.2)))
    (moduleSheaf_kernel_comp_eq_zero g f (fun x => (h x).elim
      (fun hx => Or.inl hx.2) (fun hx => Or.inr hx.1)))

theorem moduleSheafLocalQuotientIso_comm : f ≫ (moduleSheafLocalQuotientIso f g h).hom = g := by
  have := moduleSheaf_localQuotient_epi f g h
  exact Abelian.comp_epiDesc _ _ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalStalkQuasiIso.Constructions
