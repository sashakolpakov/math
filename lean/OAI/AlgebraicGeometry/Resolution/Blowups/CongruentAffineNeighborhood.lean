import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CongruenceSections

/-! # Congruent Affine Neighborhood -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Every point on the congruence subscheme has a common affine neighborhood for both maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem CongruentAffineNeighborhood.Construction.exists_common_affine_pair_of_point_eq {U X : Scheme.{u}}
    (a b : U ⟶ X) (x : U) (hx : a x = b x) :
    ∃ (W : X.affineOpens) (V : U.affineOpens),
      V.1 ≤ a ⁻¹ᵁ W.1 ∧ V.1 ≤ b ⁻¹ᵁ W.1 ∧ x ∈ V.1 := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (a x)) isOpen_univ
  have hboth : x ∈ (a ⁻¹ᵁ W ⊓ b ⁻¹ᵁ W : U.Opens) := by
    refine ⟨hxW, ?_⟩
    change b x ∈ W
    rwa [← hx]
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    U.isBasis_affineOpens.exists_subset_of_mem_open hboth (a ⁻¹ᵁ W ⊓ b ⁻¹ᵁ W).isOpen
  exact ⟨⟨W, hW⟩, ⟨V, hV⟩, fun y hy => (hVW hy).1, fun y hy => (hVW hy).2, hxV⟩

theorem IdealSheaf.CongruentMaps.Construction.IdealSheafCongruent.exists_affine_pair {U X : Scheme.{u}}
    {a b : U ⟶ X} {T : X.IdealSheafData} (h : IdealSheaf.CongruentMaps.Construction.IdealSheafCongruent a b T)
    (x : U) (hx : x ∈ (T.comap a).support) :
    ∃ (W : X.affineOpens) (V : U.affineOpens),
      ∃ (ha : V.1 ≤ a ⁻¹ᵁ W.1) (hb : V.1 ≤ b ⁻¹ᵁ W.1), x ∈ V.1 ∧
        (T.ideal W).map (a.appLE W.1 V.1 ha).hom = (T.ideal W).map (b.appLE W.1 V.1 hb).hom ∧
        ∀ z : Γ(X, W), (b.appLE W.1 V.1 hb).hom z - (a.appLE W.1 V.1 ha).hom z ∈
          (T.ideal W).map (a.appLE W.1 V.1 ha).hom := by
  obtain ⟨W, V, ha, hb, hxV⟩ := CongruentAffineNeighborhood.Construction.exists_common_affine_pair_of_point_eq a b x (h.point_eq_on_support x hx)
  exact ⟨W, V, ha, hb, hxV, h.appLE W V ha hb⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
