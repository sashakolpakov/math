import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Dual Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.DualFunctor

noncomputable section

/-! The actual module dual as an additive functor, with exactness of reversed dual complexes over fields. -/
open _root_.CategoryTheory Opposite
universe u v

def moduleDualFunctor (R : Type u) [CommRing R] : (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (Module.Dual R (unop M : ModuleCat.{u} R))
  map f := ModuleCat.ofHom f.unop.hom.dualMap
  map_id M := by
    apply ModuleCat.hom_ext
    ext ℓ x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext ℓ x
    rfl

instance moduleDualFunctor_additive (R : Type u) [CommRing R] : (moduleDualFunctor R).Additive where
  map_add {X Y f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ℓ
    change Module.Dual R (unop X : ModuleCat.{u} R) at ℓ
    apply LinearMap.ext
    intro x
    change ℓ (f.unop.hom x + g.unop.hom x) = ℓ (f.unop.hom x) + ℓ (g.unop.hom x)
    exact ℓ.map_add _ _

def dualModuleShortComplex {R : Type u} [CommRing R] (S : ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ModuleCat.{u} R) := S.op.map (moduleDualFunctor R)

theorem field_dualModuleShortComplex_exact
    {K : Type u} [Field K] (S : ShortComplex (ModuleCat.{u} K)) (hS : S.Exact) :
    (dualModuleShortComplex S).Exact := by
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  change LinearMap.range S.g.hom.dualMap = LinearMap.ker S.f.hom.dualMap
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range, hS.moduleCat_range_eq_ker]

def dualModuleComplex {R : Type u} [CommRing R] {ι : Type v} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{u} R) c) : HomologicalComplex (ModuleCat.{u} R) c.symm :=
  ((moduleDualFunctor R).mapHomologicalComplex c.symm).obj C.op

theorem field_dualModuleComplex_acyclic
    {K : Type u} [Field K] {ι : Type v} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{u} K) c) (hC : C.Acyclic) :
    (dualModuleComplex C).Acyclic := by
  intro i
  exact field_dualModuleShortComplex_exact (C.sc i) (hC i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.DualFunctor
