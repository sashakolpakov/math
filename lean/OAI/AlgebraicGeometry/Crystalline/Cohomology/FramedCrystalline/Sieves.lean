import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.CrystallineRestriction

/-! # Sieves -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Sieves.FramedCrystallineSieves

noncomputable section

/-!
# Native covering sieves and restriction of frame coordinates

Forgetting lifted coordinates commutes with pullback of generated sieves.
Every native arrow into an underlying framed object lifts after equipping
its source with the restricted coordinates. These are statements about
the existing native crystalline category and arbitrary sieves.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.CrystallineRestriction.FramedCrystallineRestriction

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)

local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.forget p k B σ a

theorem pushforward_pullback {P Q : FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ a}
    (f : P ⟶ Q) (S : Sieve Q) :
    (S.pullback f).functorPushforward U = (S.functorPushforward U).pullback ((U).map f) := by
  apply le_antisymm (Sieve.functorPushforward_pullback_le U f S)
  rintro T h ⟨Y, g, v, hg, he⟩
  let l := CrystallineRestriction.FramedCrystallineRestriction.map p k B σ a P h
  let r := CrystallineRestriction.FramedCrystallineRestriction.coneMap p k B σ a h v f g he
  have hr : l ≫ f = r ≫ g :=
    FramedCrystalline.Category.FramedCrystallineCategory.hom_ext p k B σ a he
  refine ⟨CrystallineRestriction.FramedCrystallineRestriction.object p k B σ a P h, l, 𝟙 T, ?_, ?_⟩
  · change S (l ≫ f)
    rw [hr]
    exact S.downward_closed hg r
  · exact Category.id_comp h

theorem pushforward_functorPullback (Q : FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ a)
    (S : Sieve Q.base) : (S.functorPullback U).functorPushforward U = S := by
  apply le_antisymm (Sieve.functorPullback_pushforward_le U S)
  intro P f hf
  exact ⟨CrystallineRestriction.FramedCrystallineRestriction.object p k B σ a Q f, CrystallineRestriction.FramedCrystallineRestriction.map p k B σ a Q f, 𝟙 P, hf, Category.id_comp f⟩

theorem functorPullback_pushforward (Q : FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ a)
    (S : Sieve Q) : (S.functorPushforward U).functorPullback U = S := by
  apply le_antisymm _ (Sieve.le_functorPushforward_pullback U S)
  rintro P f ⟨Y, g, v, hg, he⟩
  let l : P ⟶ Y :=
    { hom := v
      coordinate_comm := fun i => by
        have hi := congrArg (fun h : P.base ⟶ Q.base => h.ambientMap (Q.coordinate i)) he
        change f.hom.ambientMap (Q.coordinate i) = v.ambientMap (g.hom.ambientMap (Q.coordinate i)) at hi
        rw [f.coordinate_comm, g.coordinate_comm] at hi
        exact hi.symm }
  have hf : f = l ≫ g := FramedCrystalline.Category.FramedCrystallineCategory.hom_ext p k B σ a he
  rw [hf]
  exact S.downward_closed hg l

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Sieves.FramedCrystallineSieves
