import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ConstantSections
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Homology.Functor

/-! # Complex Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexMap

noncomputable section

/-!
# IntegralComparison: a map from a constant sheaf complex induces a coefficient-linear section map
-/

open _root_.CategoryTheory

universe u v w z

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]
  [HasExt.{max w z} (Sheaf J (ModuleCat.{w} R))]
  (D : CochainComplex (ModuleCat.{w} R) ℕ) (K : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ)
  (a : ((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (ComplexShape.up ℕ)).obj D ⟶ K)

def source : CochainComplex (ModuleCat.{max w z} R) ℕ :=
  ((ModuleCat.uliftFunctor.{z, w} R).mapHomologicalComplex (ComplexShape.up ℕ)).obj D

def target : CochainComplex (ModuleCat.{max w z} R) ℕ :=
  ((Ext.ModuleFunctor.functor R (Module.ConstantSections.constantUnit R J) 0).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K

def map : source R D ⟶ target R J K where
  f n := ModuleCat.ofHom
    ((Module.ConstantSections.sectionMap R J (D.X n) (K.X n) (a.f n)).comp ULift.moduleEquiv.toLinearMap)
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Module.ConstantSections.section_natural R J (D.d n m) (K.d n m) (a.f n) (a.f m)
      (a.comm n m).symm x.down

theorem map_f_apply (n : ℕ) (x : (source R D).X n) :
    (map R J D K a).f n x = Module.ConstantSections.sectionMap R J (D.X n) (K.X n) (a.f n) x.down := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexMap
