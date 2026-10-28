import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactImageOpenRestriction

/-! # Open Compact Stage Descent -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenCompactStageDescent.Constructions

noncomputable section

/-! Actual compact open extension recovers relative classes, and commuting support stages descend through source excision. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

theorem relativePullback_compactOpenExtension {X Y : TopCat.{0}} [T2Space Y]
    (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f) (K : Compacts X) (L : Compacts Y)
    (hL : f '' (K : Set X) = (L : Set Y))
    (hm : Set.MapsTo f (K : Set X)ᶜ (L : Set Y)ᶜ) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hm n ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K n ≫
        OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension f hf n =
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) Y L n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  exact OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_pullback f hf K L hL hm n b

theorem compactStageSquare_desc {C : Type*} [Category C]
    {G L T R S A : C} (e : G ≅ L) (s : L ⟶ S) (i : G ⟶ S)
    (g : G ⟶ T) (t : L ⟶ R) (r : T ⟶ R) (j : R ⟶ A) (k : T ⟶ A) (F : S ⟶ A)
    (hs : e.hom ≫ s = i) (ht : e.hom ≫ t = g ≫ r)
    (hr : r ≫ j = k) (hF : i ≫ F = g ≫ k) : s ≫ F = t ≫ j := by
  apply (cancel_epi e.hom).mp
  calc
    e.hom ≫ s ≫ F = i ≫ F := by rw [← Category.assoc, hs]
    _ = g ≫ k := hF
    _ = g ≫ r ≫ j := by rw [hr]
    _ = e.hom ≫ t ≫ j := by rw [← Category.assoc, ← ht, Category.assoc]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenCompactStageDescent.Constructions
