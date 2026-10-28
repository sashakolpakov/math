import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsPushforward
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCech

/-! # Ordered Cech Pushforward -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechPushforward

noncomputable section

/-! The original supported Cech comparison is unchanged when a
sheaf is pushed forward and the open diagram is pulled back. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
abbrev pushed (R : Type u) [CommRing R] {X Y : TopCat.{v}} (f : Y ⟶ X)
    (K : CochainComplex (Sheaf (Opens.grothendieckTopology Y)
      (ModuleCat.{max u v z} R)) ℕ) := SectionsPushforward.pushed f K

variable (R : Type u) [CommRing R] {X Y : TopCat.{v}} (f : Y ⟶ X)
  {C : Type w} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {ι : Type w} [LinearOrder ι] (U : ι → C) (O : Opens X)
  (K : CochainComplex (Sheaf (Opens.grothendieckTopology Y)
    (ModuleCat.{max u v w z} R)) ℕ)

abbrev pulled : C ⥤ Opens Y := F ⋙ SectionsPushforward.preimage f

def sourceIso : OrderedCechEdge.source.{u,v,w,z} R X F O (pushed.{u,v,max w z} R f K) ≅
    OrderedCechEdge.source.{u,v,w,z} R Y (pulled f F)
      ((SectionsPushforward.preimage f).obj O) K := Iso.refl _

def presheafIso : OrderedCechEdge.presheafComplex.{u,v,w,z} R X F (pushed.{u,v,max w z} R f K) ≅
    OrderedCechEdge.presheafComplex.{u,v,w,z} R Y (pulled f F) K := Iso.refl _

def totalIso : (OrderedCechEdge.bicomplex.{u,v,w,z} R X F U (pushed.{u,v,max w z} R f K)).total (.up ℕ) ≅
    (OrderedCechEdge.bicomplex.{u,v,w,z} R Y (pulled f F) U K).total (.up ℕ) := Iso.refl _

variable (hO : ∀ i, F.obj (U i) ≤ O)
  (hcover : F.obj (⊤_ C) ⊓ O ≤ ⨆ i, F.obj (U i))
  (hrows : ∀ q r, ((OrderedCechEdge.bicomplex.{u,v,w,z} R X F U (pushed.{u,v,max w z} R f K)).X q).ExactAt (r+1))
  (hglobal : F.obj (⊤_ C) ⊔ O = ⊤)

include hO in
omit [HasFiniteProducts C] [LinearOrder ι] in
theorem pulled_below (i : ι) :
    (pulled f F).obj (U i) ≤ (SectionsPushforward.preimage f).obj O :=
  leOfHom ((SectionsPushforward.preimage f).map (homOfLE (hO i)))

include hcover in
omit [LinearOrder ι] in
theorem pulled_cover :
    (pulled f F).obj (⊤_ C) ⊓ (SectionsPushforward.preimage f).obj O ≤
      ⨆ i, (pulled f F).obj (U i) := by
  change (Opens.map f).obj (F.obj (⊤_ C) ⊓ O) ≤ ⨆ i, (Opens.map f).obj (F.obj (U i))
  calc
    _ ≤ (Opens.map f).obj (⨆ i, F.obj (U i)) :=
      leOfHom ((Opens.map f).map (homOfLE hcover))
    _ = _ := Opens.map_iSup f (fun i => F.obj (U i))

include hrows in
theorem pulled_rows : ∀ q r,
    ((OrderedCechEdge.bicomplex.{u,v,w,z} R Y (pulled f F) U K).X q).ExactAt (r+1) := hrows

include hglobal in
theorem pulled_global :
    (pulled f F).obj (⊤_ C) ⊔ (SectionsPushforward.preimage f).obj O = ⊤ :=
  SectionsPushforward.preimage_cover f O (F.obj (⊤_ C)) hglobal

theorem edge :
    OrderedCechEdge.map.{u,v,w,z} R X F U O (pushed.{u,v,max w z} R f K) hO ≫ (totalIso.{u,v,w,z} R f F U K).hom =
    (sourceIso.{u,v,w,z} R f F O K).hom ≫
      OrderedCechEdge.map.{u,v,w,z} R Y (pulled f F) U
        ((SectionsPushforward.preimage f).obj O) K (pulled_below f F U O hO) := by
  change OrderedCechEdge.map.{u,v,w,z} R X F U O (pushed.{u,v,max w z} R f K) hO ≫ 𝟙 _ =
    𝟙 _ ≫ OrderedCechEdge.map.{u,v,w,z} R Y (pulled f F) U
      ((SectionsPushforward.preimage f).obj O) K (pulled_below f F U O hO)
  rw [Category.comp_id, Category.id_comp]
  rfl

theorem forgetSupport (q : ℕ) :
    OrderedCech.Comparison.forgetSupport.{u,v,w,z} R X F U O (pushed.{u,v,max w z} R f K)
      hO hcover hrows hglobal q ≫
        homologyMap (SectionsPushforward.globalIso f K).hom q =
    homologyMap (totalIso.{u,v,w,z} R f F U K).hom q ≫
      OrderedCech.Comparison.forgetSupport.{u,v,w,z} R Y (pulled f F) U
        ((SectionsPushforward.preimage f).obj O) K
        (pulled_below f F U O hO) (pulled_cover f F U O hcover)
        (pulled_rows.{u,v,w,z} R f F U K hrows) (pulled_global f F O hglobal) q := by
  change OrderedCech.Comparison.forgetSupport.{u,v,w,z} R X F U O (pushed.{u,v,max w z} R f K)
      hO hcover hrows hglobal q ≫ homologyMap (𝟙 _) q =
    homologyMap (𝟙 _) q ≫ _
  rw [homologyMap_id, homologyMap_id, Category.comp_id, Category.id_comp]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechPushforward
