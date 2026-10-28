import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleCoefficientNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechTopClass
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Single Top Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.SingleTopNaturality

noncomputable section

/-! The original single-total coordinates, with an explicit degree
transport, preserve the full-intersection class under coefficient maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] [Fintype ι] (U : ι → C)
  {R : Type v} [CommRing R] [HasProducts.{u} (ModuleCat.{w} R)]
  (N : Cᵒᵖ ⥤ ModuleCat.{w} R) (c m q : ℕ) (hq : q=m+c)

def coordinates :
    ((Functor.SingleTotal.bicomplex (AugmentedOrdered.CechFunctor.functor U) N c).total
      (.up ℕ)).homology q ≅ (AugmentedOrdered.Cech.complex U N).homology m :=
  eqToIso (congrArg (fun j =>
    ((Functor.SingleTotal.bicomplex (AugmentedOrdered.CechFunctor.functor U) N c).total
      (.up ℕ)).homology j) hq) ≪≫
    Functor.SingleTotal.homologyIso (AugmentedOrdered.CechFunctor.functor U) N c m

variable {N} {M : Cᵒᵖ ⥤ ModuleCat.{w} R} (a : N ⟶ M)

omit [Fintype ι] in
theorem naturality :
    homologyMap (Functor.SingleCoefficientNaturality.totalMap
      (AugmentedOrdered.CechFunctor.functor U) a c) q ≫ (coordinates U M c m q hq).hom =
    (coordinates U N c m q hq).hom ≫
      homologyMap (AugmentedOrdered.CechFunctor.complexMap U a) m := by
  subst q
  exact Functor.SingleCoefficientNaturality.homology_naturality
    (AugmentedOrdered.CechFunctor.functor U) a c m

theorem topClass (hm : Fintype.card ι=m)
    (x : ((Functor.SingleTotal.bicomplex (AugmentedOrdered.CechFunctor.functor U) N c).total
      (.up ℕ)).homology q)
    (z : N.obj (op (AugmentedOrdered.CechCoordinates.topObject U m hm))) (s : ℤˣ)
    (hx : (coordinates U N c m q hq).hom x =
      s • AugmentedOrdered.CechTopClass.topClass U N m hm z) :
    (coordinates U M c m q hq).hom
      (homologyMap (Functor.SingleCoefficientNaturality.totalMap
        (AugmentedOrdered.CechFunctor.functor U) a c) q x) =
    s • AugmentedOrdered.CechTopClass.topClass U M m hm
      (a.app (op (AugmentedOrdered.CechCoordinates.topObject U m hm)) z) := by
  have h := ConcreteCategory.congr_hom (naturality U c m q hq a) x
  simp only [ConcreteCategory.comp_apply] at h
  rw [hx] at h
  refine h.trans ?_
  simp only [Units.smul_def, map_zsmul]
  exact congrArg (fun y => (s : ℤ) • y)
    (AugmentedOrdered.CechTopClass.topClass_naturality U N m hm a z)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.SingleTopNaturality
