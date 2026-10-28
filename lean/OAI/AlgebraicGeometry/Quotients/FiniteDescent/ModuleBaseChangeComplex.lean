import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.Preadditive
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Module Base Change Complex -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting

noncomputable section

/-! The tensor-product base-change functor on module short complexes. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]

def moduleBaseChangeFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} K where
  obj M := ModuleCat.of K (K ⊗[R] M)
  map f := ModuleCat.ofHom (f.hom.baseChange K)
  map_id M := by
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_comp f.hom g.hom

instance moduleBaseChangeFunctor_additive : (moduleBaseChangeFunctor R K).Additive where
  map_add := by
    intros
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_add _ _

abbrev moduleBaseChangeComplex (S : ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ModuleCat.{u} K) :=
  (moduleBaseChangeFunctor R K).mapShortComplex.obj S

theorem moduleBaseChangeComplex_f_zero (S : ShortComplex (ModuleCat.{u} R))
    (hf : S.f.hom.baseChange K = 0) : (moduleBaseChangeComplex R K S).f = 0 :=
  ModuleCat.hom_ext hf

theorem moduleBaseChangeComplex_g_zero (S : ShortComplex (ModuleCat.{u} R))
    (hg : S.g.hom.baseChange K = 0) : (moduleBaseChangeComplex R K S).g = 0 :=
  ModuleCat.hom_ext hg

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting
