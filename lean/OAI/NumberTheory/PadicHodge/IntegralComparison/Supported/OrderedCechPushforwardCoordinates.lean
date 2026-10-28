import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechPushforward

/-! # Ordered Cech Pushforward Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechPushforwardCoordinates

noncomputable section

/-! The original pushforward coordinate map is literally the identity
on the supported Cech total and hence on its homology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
variable (R : Type u) [CommRing R] {X Y : TopCat.{v}} (f : Y ⟶ X)
  {C : Type w} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {ι : Type w} [LinearOrder ι] (U : ι → C)
  (K : CochainComplex (Sheaf (Opens.grothendieckTopology Y)
    (ModuleCat.{max u v w z} R)) ℕ)

theorem total_homology (q : ℕ) :
    homologyMap (OrderedCechPushforward.totalIso.{u,v,w,z} R f F U K).hom q =
      𝟙 (((OrderedCechEdge.bicomplex.{u,v,w,z} R X F U
        (OrderedCechPushforward.pushed.{u,v,max w z} R f K)).total (.up ℕ)).homology q) := by
  change homologyMap (𝟙 _) q = _
  exact homologyMap_id _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechPushforwardCoordinates
