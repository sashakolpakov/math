import OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.ResolutionFaceMaps
import Mathlib.Algebra.Category.ModuleCat.Products

/-! # Differential -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.Differential

noncomputable section

/-! The actual frame Čech differential in product-section coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.AlgebraicTopology Simplicial

universe u v w

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {ι : Type v} (F : ι → C) (R : Type (max u v)) [CommRing R]

local instance moduleProducts : HasProducts.{v} (ModuleCat.{max u v} R) := by
  let h : HasLimitsOfSize.{v, v} (ModuleCat.{max u v} R) :=
    ModuleCat.hasLimitsOfSize.{v, v, max u v, max u v}
  exact fun I => h.has_limits_of_shape (Discrete I)

variable (H : Cᵒᵖ ⥤ ModuleCat.{max u v} R)

def complex : CochainComplex (ModuleCat.{max u v} R) ℕ :=
  (NonemptyCechNerve.complexFunctor F).obj H

def coordinate (n : ℕ) (t : Fin (n + 1) → ι) : (complex F R H).X n ⟶
    H.obj (op (Presentation.TupleProducts.family F n t)) :=
  Pi.π (fun t => H.obj (op (Presentation.TupleProducts.family F n t))) t

theorem differential (n : ℕ) : (complex F R H).d n (n + 1) =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      ((FormalCoproduct.cosimplicialObjectFunctor (NonemptyCechNerve.nerve F)).obj H).δ i := by
  change (AlternatingCofaceMapComplex.obj
    ((FormalCoproduct.cosimplicialObjectFunctor (NonemptyCechNerve.nerve F)).obj H)).d n (n + 1) = _
  simp only [AlternatingCofaceMapComplex.obj, CochainComplex.of_d, AlternatingCofaceMapComplex.objD]

theorem coface (n : ℕ) (i : Fin (n + 2)) (t : Fin (n + 2) → ι) :
    ((FormalCoproduct.cosimplicialObjectFunctor (NonemptyCechNerve.nerve F)).obj H).δ i ≫
      coordinate F R H (n + 1) t = coordinate F R H n (t ∘ i.succAbove) ≫
        H.map (Presentation.ResolutionFaceMaps.productMap F i.succAbove t).op :=
  Pi.lift_comp_π _ t

private def homEvaluation {S : Type w} [CommRing S] {A B : ModuleCat.{w} S} (x : A) : (A ⟶ B) →+ B where
  toFun f := f x
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coordinates (n : ℕ) (t : Fin (n + 2) → ι) (x : (complex F R H).X n) :
    coordinate F R H (n + 1) t ((complex F R H).d n (n + 1) x) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        H.map (Presentation.ResolutionFaceMaps.productMap F i.succAbove t).op
          (coordinate F R H n (t ∘ i.succAbove) x) := by
  have h : (complex F R H).d n (n + 1) ≫ coordinate F R H (n + 1) t =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (coordinate F R H n (t ∘ i.succAbove) ≫
        H.map (Presentation.ResolutionFaceMaps.productMap F i.succAbove t).op) := by
    refine (congrArg (fun f => f ≫ coordinate F R H (n + 1) t) (differential F R H n)).trans ?_
    refine (Preadditive.sum_comp _ _ _).trans ?_
    apply Finset.sum_congr rfl
    intro i _
    exact (Preadditive.zsmul_comp _ _ _).trans
      (congrArg (fun f => (-1 : ℤ) ^ (i : ℕ) • f) (coface F R H n i t))
  refine (congrArg (fun f => f x) h).trans ?_
  let ev : ((complex F R H).X n ⟶ H.obj (op (Presentation.TupleProducts.family F (n + 1) t))) →+
      H.obj (op (Presentation.TupleProducts.family F (n + 1) t)) := homEvaluation x
  refine (map_sum ev
    (fun i : Fin (n + 2) => (-1 : ℤ) ^ (i : ℕ) • (coordinate F R H n (t ∘ i.succAbove) ≫
      H.map (Presentation.ResolutionFaceMaps.productMap F i.succAbove t).op)) Finset.univ).trans ?_
  apply Finset.sum_congr rfl
  intro i _
  exact map_zsmul ev _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.Differential
