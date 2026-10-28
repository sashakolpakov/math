import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.HomologyFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyEndpoints

/-! # Local -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.Local.Comparison

noncomputable section

/-! Assemble local comparison identities before choosing a supported
Čech family or passing to its cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v v' w
variable {R : Type u} [CommRing R]
  {C : Type v} [Preorder C] [HasFiniteProducts C]
  {C' : Type v'} [Preorder C']
  [HasProducts.{v} (ModuleCat.{w} R)]
  (G : CochainComplex (C'ᵒᵖ ⥤ ModuleCat.{w} R) ℕ ⥤
    CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ)
  {K A B I : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ}
  {K' B' I' : CochainComplex (C'ᵒᵖ ⥤ ModuleCat.{w} R) ℕ}
  (s : I ≅ G.obj I')
  {q : K ⟶ I} {p : K ⟶ A} {a : A ⟶ I} {f : A ⟶ B} {b : B ⟶ I}
  {sB : B ⟶ G.obj B'} {r : K ⟶ G.obj K'}
  {p' : K' ⟶ B'} {a' : B' ⟶ I'} {q' : K' ⟶ I'}
  (hq : q = p ≫ a) (hq' : q' = p' ≫ a')
  (hi : Homotopy a (f ≫ b))
  (hb : b ≫ s.hom = sB ≫ G.map a')
  (hp : (p ≫ f) ≫ sB = r ≫ G.map p')

include hq hq' hi hb hp in
theorem comparison (ι : Type v) [LinearOrder ι] (U : ι → C) (n : ℕ) :
    (HomologyFunctor.functor U n).map q =
      (HomologyFunctor.functor U n).map ((r ≫ G.map q') ≫ s.inv) := by
  let F := HomologyFunctor.functor.{u,v,w} (R := R) U n
  apply CohomologyEndpoints.Comparison.mapped_transport F G s
  exact CohomologyEndpoints.Comparison.eq (F.mapIso s)
    (HomologyFunctor.MappedComparisonEquality.factorization F hq)
    (HomologyFunctor.MappedComparisonEquality.factorization (G ⋙ F) hq')
    (HomologyFunctor.homotopy_comp U hi n)
    (HomologyFunctor.MappedComparisonEquality.square F hb)
    (HomologyFunctor.MappedComparisonEquality.triple F hp)

include hq hq' hi in
theorem from_incoming (sB : B ⟶ G.obj B') (r : K ⟶ G.obj K')
    (hb : b ≫ s.hom = sB ≫ G.map a')
    (hp : (p ≫ f) ≫ sB = r ≫ G.map p')
    (ι : Type v) [LinearOrder ι] (U : ι → C) (n : ℕ) :
    (HomologyFunctor.functor U n).map q =
      (HomologyFunctor.functor U n).map ((r ≫ G.map q') ≫ s.inv) :=
  comparison G s hq hq' hi hb hp ι U n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.Local.Comparison
