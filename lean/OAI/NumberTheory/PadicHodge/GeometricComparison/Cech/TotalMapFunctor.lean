import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalOneQuasiIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalMap

/-! # Total Map Functor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalMapFunctor.CechTotalMapFunctor

noncomputable section

/-! The original Cech total is a functor preserving zero maps, so original
cochain vanishing identities survive passage to its total complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

private theorem functorThreeZero {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {K L M N : C} (a : K ⟶ L) (b : L ⟶ M) (c : M ⟶ N) (h : a ≫ b ≫ c = 0) :
    F.map a ≫ F.map b ≫ F.map c = 0 := by
  rw [← F.map_comp, ← F.map_comp, h, F.map_zero]

universe u v s t
variable (R : Type u) [CommRing R] {C : Type s} [Category.{t} C]
  (E : SimplicialObject (FormalCoproduct.{0} C))

local instance limits : HasLimitsOfSize.{0, 0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasLimitsOfSize.{0, 0, max u v, u}

local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasColimitsOfSize.{max u v, u, 0, 0} R

def functor : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ ⥤
    CochainComplex (ModuleCat.{max u v} R) ℕ :=
  TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{u, v} R E ⋙
    HomologicalComplex₂.totalFunctor (ModuleCat.{max u v} R) (.up ℕ) (.up ℕ) (.up ℕ)

local instance bicomplex_additive : (TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{u, v} R E).Additive := by
  dsimp only [TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex]
  infer_instance

instance preservesZero : (functor.{u, v} R E).PreservesZeroMorphisms where
  map_zero K L := by
    change HomologicalComplex₂.total.map ((TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{u, v} R E).map (0 : K ⟶ L)) (.up ℕ) = 0
    rw [Functor.map_zero]
    exact TotalMap.TotalMapZero.zero _ _

variable {K L M N : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ}

theorem map_eq (a : K ⟶ L) : (functor.{u, v} R E).map a = TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{u, v} R E a := rfl

theorem three_zero (a : K ⟶ L) (b : L ⟶ M) (c : M ⟶ N) (h : a ≫ b ≫ c = 0) :
    TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{u, v} R E a ≫ TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{u, v} R E b ≫
      TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{u, v} R E c = 0 :=
  functorThreeZero (functor.{u, v} R E) a b c h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalMapFunctor.CechTotalMapFunctor
