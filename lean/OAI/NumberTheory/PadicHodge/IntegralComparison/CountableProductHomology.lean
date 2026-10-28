import OAI.NumberTheory.PadicHodge.IntegralComparison.CountableModuleProduct
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Countable Product Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CountableProductHomology

noncomputable section

/-!
# IntegralComparison: cohomology of a countable product of module complexes
-/

open _root_.CategoryTheory

universe u

variable (R : Type u) [CommRing R] (K : CochainComplex (Discrete ℕ ⥤ ModuleCat.{u} R) ℕ)

def complex : CochainComplex (ModuleCat.{u} R) ℕ :=
  ((CountableModuleProduct.functor R).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

def component (n : ℕ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  (((evaluation (Discrete ℕ) (ModuleCat.{u} R)).obj ⟨n⟩).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

def homologyIso (i : ℕ) : (complex R K).homology i ≅ ModuleCat.of R (∀ n, (component R K n).homology i) :=
  (K.sc i).mapHomologyIso (CountableModuleProduct.functor R) ≪≫
    (LinearEquiv.piCongrRight (fun n => ((K.sc i).mapHomologyIso
      ((evaluation (Discrete ℕ) (ModuleCat.{u} R)).obj ⟨n⟩)).symm.toLinearEquiv)).toModuleIso

def projection (n : ℕ) : complex R K ⟶ component R K n :=
  (NatTrans.mapHomologicalComplex (CountableModuleProduct.projection R n) (ComplexShape.up ℕ)).app K

theorem homologyIso_projection (i n : ℕ) :
    (homologyIso R K i).hom ≫ ModuleCat.ofHom (LinearMap.proj n) =
      HomologicalComplex.homologyMap (projection R K n) i :=
  ((K.sc i).homologyMap_mapNatTrans (CountableModuleProduct.projection R n)).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CountableProductHomology
