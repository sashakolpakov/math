import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.Local

/-! # From Incoming Square -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.FromIncomingSquare

noncomputable section

/-! Fix an incoming comparison square before choosing the source
complexes, factorizations, and supported Čech family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v v' w
variable {R : Type u} [CommRing R]
  {C : Type v} [Preorder C] [HasFiniteProducts C]
  {C' : Type v'} [Preorder C']
  [HasProducts.{v} (ModuleCat.{w} R)]
  (G : CochainComplex (C'ᵒᵖ ⥤ ModuleCat.{w} R) ℕ ⥤
    CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ)
  {B I : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ}
  {B' I' : CochainComplex (C'ᵒᵖ ⥤ ModuleCat.{w} R) ℕ}
  (s : I ≅ G.obj I') (b : B ⟶ I) (a' : B' ⟶ I') (sB : B ⟶ G.obj B')

theorem comparison (hb : b ≫ s.hom = sB ≫ G.map a')
    (K A : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ)
    (K' : CochainComplex (C'ᵒᵖ ⥤ ModuleCat.{w} R) ℕ)
    (q : K ⟶ I) (p : K ⟶ A) (a : A ⟶ I) (f : A ⟶ B)
    (p' : K' ⟶ B') (q' : K' ⟶ I') (r : K ⟶ G.obj K')
    (hq : q = p ≫ a) (hq' : q' = p' ≫ a')
    (hi : Homotopy a (f ≫ b)) (hp : (p ≫ f) ≫ sB = r ≫ G.map p')
    (ι : Type v) [LinearOrder ι] (U : ι → C) (n : ℕ) :
    (HomologyFunctor.functor U n).map q =
      (HomologyFunctor.functor U n).map ((r ≫ G.map q') ≫ s.inv) :=
  Local.Comparison.comparison G s hq hq' hi hb hp ι U n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.FromIncomingSquare
