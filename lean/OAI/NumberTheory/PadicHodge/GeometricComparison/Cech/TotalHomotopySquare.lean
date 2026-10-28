import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalHomotopyOne

/-! # Total Homotopy Square -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalHomotopySquare.CechTotalHomotopySquare

noncomputable section

/-! A homotopy-commutative square of presheaf complexes induces a
commutative square on the original Cech total H-one. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Simplicial

universe u v s t
variable (R : Type u) [CommRing R] {C : Type s} [Category.{t} C]
  (E : SimplicialObject (FormalCoproduct.{0} C))

def functor : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ ⥤ CochainComplex (ModuleCat.{max u v} R) ℕ :=
  TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex R E ⋙
    HomologicalComplex₂.totalFunctor (ModuleCat.{max u v} R) (.up ℕ) (.up ℕ) (.up ℕ)

theorem map_comp {K L M : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ}
    (a : K ⟶ L) (b : L ⟶ M) : TotalOneQuasiIso.CechTotalHOneQuasiIso.map R E (a ≫ b) =
      TotalOneQuasiIso.CechTotalHOneQuasiIso.map R E a ≫ TotalOneQuasiIso.CechTotalHOneQuasiIso.map R E b :=
  (congrArg (fun q => HomologicalComplex₂.total.map q (.up ℕ))
    ((TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex R E).map_comp a b)).trans
      (HomologicalComplex₂.total.map_comp _ _ (.up ℕ))

theorem homology_comp {K L M : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ}
    (a : K ⟶ L) (b : L ⟶ M) : HomologicalComplex.homologyMap (TotalOneQuasiIso.CechTotalHOneQuasiIso.map R E (a ≫ b)) 1 =
      HomologicalComplex.homologyMap (TotalOneQuasiIso.CechTotalHOneQuasiIso.map R E a) 1 ≫
        HomologicalComplex.homologyMap (TotalOneQuasiIso.CechTotalHOneQuasiIso.map R E b) 1 :=
  (congrArg (fun q => HomologicalComplex.homologyMap q 1) (CechTotalHomotopySquare.map_comp R E a b)).trans
    (HomologicalComplex.homologyMap_comp _ _ 1)

variable {K L M N : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ}
  (a : K ⟶ L) (b : L ⟶ N) (c : K ⟶ M) (d : M ⟶ N)
  (h : Homotopy (a ≫ b) (c ≫ d))

include h in
theorem homology : HomologicalComplex.homologyMap (TotalOneQuasiIso.CechTotalHOneQuasiIso.map R E a) 1 ≫
    HomologicalComplex.homologyMap (TotalOneQuasiIso.CechTotalHOneQuasiIso.map R E b) 1 =
      HomologicalComplex.homologyMap (TotalOneQuasiIso.CechTotalHOneQuasiIso.map R E c) 1 ≫
        HomologicalComplex.homologyMap (TotalOneQuasiIso.CechTotalHOneQuasiIso.map R E d) 1 := by
  exact (homology_comp R E a b).symm.trans
    ((TotalHomotopyOne.CechTotalHomotopyHOne.homology R E h).trans (homology_comp R E c d))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalHomotopySquare.CechTotalHomotopySquare
