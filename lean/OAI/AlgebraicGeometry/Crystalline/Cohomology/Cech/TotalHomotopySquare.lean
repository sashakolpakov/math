import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalHomotopy

/-! # Total Homotopy Square -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalHomotopySquare.CechTotalHomotopySquare

noncomputable section

/-! A homotopy-commutative square of presheaf complexes induces a
commutative square on the original Cech total cohomology in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Simplicial

universe u v s t
variable (R : Type u) [CommRing R] {C : Type s} [Category.{t} C]
  (E : SimplicialObject (FormalCoproduct.{0} C))

def functor : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ ⥤ CochainComplex (ModuleCat.{max u v} R) ℕ :=
  TotalQuasiIso.CechTotalQuasiIso.bicomplex R E ⋙
    HomologicalComplex₂.totalFunctor (ModuleCat.{max u v} R) (.up ℕ) (.up ℕ) (.up ℕ)

theorem map_comp {K L M : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ}
    (a : K ⟶ L) (b : L ⟶ M) : TotalQuasiIso.CechTotalQuasiIso.map R E (a ≫ b) =
      TotalQuasiIso.CechTotalQuasiIso.map R E a ≫ TotalQuasiIso.CechTotalQuasiIso.map R E b :=
  (congrArg (fun q => HomologicalComplex₂.total.map q (.up ℕ))
    ((TotalQuasiIso.CechTotalQuasiIso.bicomplex R E).map_comp a b)).trans
      (HomologicalComplex₂.total.map_comp _ _ (.up ℕ))

theorem homology_comp {K L M : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ}
    (a : K ⟶ L) (b : L ⟶ M) (i : ℕ) : HomologicalComplex.homologyMap (TotalQuasiIso.CechTotalQuasiIso.map R E (a ≫ b)) i =
      HomologicalComplex.homologyMap (TotalQuasiIso.CechTotalQuasiIso.map R E a) i ≫
        HomologicalComplex.homologyMap (TotalQuasiIso.CechTotalQuasiIso.map R E b) i :=
  (congrArg (fun q => HomologicalComplex.homologyMap q i) (CechTotalHomotopySquare.map_comp R E a b)).trans
    (HomologicalComplex.homologyMap_comp _ _ i)

variable {K L M N : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ}
  (a : K ⟶ L) (b : L ⟶ N) (c : K ⟶ M) (d : M ⟶ N)
  (h : Homotopy (a ≫ b) (c ≫ d))

include h in
theorem homology (i : ℕ) : HomologicalComplex.homologyMap (TotalQuasiIso.CechTotalQuasiIso.map R E a) i ≫
    HomologicalComplex.homologyMap (TotalQuasiIso.CechTotalQuasiIso.map R E b) i =
      HomologicalComplex.homologyMap (TotalQuasiIso.CechTotalQuasiIso.map R E c) i ≫
        HomologicalComplex.homologyMap (TotalQuasiIso.CechTotalQuasiIso.map R E d) i := by
  exact (homology_comp R E a b i).symm.trans
    ((TotalHomotopy.CechTotalHomotopy.homology R E h i).trans (homology_comp R E c d i))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalHomotopySquare.CechTotalHomotopySquare
