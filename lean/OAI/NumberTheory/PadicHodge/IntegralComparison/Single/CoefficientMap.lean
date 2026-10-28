import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Coefficient Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Single.CoefficientMap

noncomputable section

/-! A coefficient functor carries the genuine map from a single object
with its original retained component and inverse single coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
universe u v w z
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] (N : C) (c : ℕ) (K : CochainComplex C ℕ)
  (a : (single C (.up ℕ) c).obj N ⟶ K)

def map : (single D (.up ℕ) c).obj (F.obj N) ⟶
    (F.mapHomologicalComplex (.up ℕ)).obj K :=
  (singleMapHomologicalComplex F (.up ℕ) c).inv.app N ≫
    (F.mapHomologicalComplex (.up ℕ)).map a

theorem self (b : N ⟶ K.X c)
    (ha : a.f c = (singleObjXSelf (.up ℕ) c N).hom ≫ b) :
    (CoefficientMap.map F N c K a).f c = (singleObjXSelf (.up ℕ) c (F.obj N)).hom ≫ F.map b := by
  rw [CoefficientMap.map, comp_f, singleMapHomologicalComplex_inv_app_self]
  change (_ ≫ _) ≫ F.map (a.f c) = _
  rw [ha, F.map_comp]
  simp only [Category.assoc, ← F.map_comp, Iso.inv_hom_id_assoc]

theorem inverse_self (b : N ⟶ K.X c)
    (ha : a.f c = (singleObjXSelf (.up ℕ) c N).hom ≫ b) :
    (singleObjXSelf (.up ℕ) c (F.obj N)).inv ≫ (CoefficientMap.map F N c K a).f c = F.map b := by
  exact (congrArg (fun f => (singleObjXSelf (.up ℕ) c (F.obj N)).inv ≫ f)
    (self F N c K a b ha)).trans
      (Iso.inv_hom_id_assoc (singleObjXSelf (.up ℕ) c (F.obj N)) (F.map b))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Single.CoefficientMap
