import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Embedding

/-! # Open Lift -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.OpenLift.CrystallineOpenLift

noncomputable section

/-!
# Lifting native crystalline objects into an open subscheme

An object whose residual open lies in the given open subscheme has an
actual lift to its crystalline site. The image of this lift is canonically
isomorphic to the original object, with identical ambient PD rings.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {X Y : Over (Spec (CommRingCat.of k))} (j : X ⟶ Y) [IsOpenImmersion j.left]
  (Q : Site.Object p k Y) (hQ : Set.range Q.immersion ⊆ Set.range j.left)

def object : Site.Object p k X where
  residueRing := Q.residueRing
  thickening := Q.thickening
  immersion := IsOpenImmersion.lift j.left Q.immersion hQ
  over_base := by
    rw [← j.w, ← Category.assoc, IsOpenImmersion.lift_fac, Q.over_base]

def iso : (Embedding.CrystallineOpenEmbedding.functor p k j).obj (object p k j Q hQ) ≅ Q where
  hom :=
    { reducedMap := AlgHom.id k Q.residueRing
      ambientMap := AlgHom.id (WittVector p k) Q.thickening.ring
      reduction_comm := fun _ => rfl
      dp_comp := (DividedPowers.DPMorphism.id Q.thickening.dividedPowers).isDPMorphism
      over_X := by
        change Spec.map (𝟙 Q.residueRing) ≫ Q.immersion =
          IsOpenImmersion.lift j.left Q.immersion hQ ≫ j.left
        rw [Spec.map_id, Category.id_comp, IsOpenImmersion.lift_fac] }
  inv :=
    { reducedMap := AlgHom.id k Q.residueRing
      ambientMap := AlgHom.id (WittVector p k) Q.thickening.ring
      reduction_comm := fun _ => rfl
      dp_comp := (DividedPowers.DPMorphism.id Q.thickening.dividedPowers).isDPMorphism
      over_X := by
        change Spec.map (𝟙 Q.residueRing) ≫
          (IsOpenImmersion.lift j.left Q.immersion hQ ≫ j.left) = Q.immersion
        rw [Spec.map_id, Category.id_comp, IsOpenImmersion.lift_fac] }
  hom_inv_id := Site.Object.Hom.ext _ _ rfl rfl
  inv_hom_id := Site.Object.Hom.ext _ _ rfl rfl

omit hQ in
theorem range_of_map (P : Site.Object p k X)
    (f : Q ⟶ (Embedding.CrystallineOpenEmbedding.functor p k j).obj P) :
    Set.range Q.immersion ⊆ Set.range j.left := by
  intro x hx
  obtain ⟨z, rfl⟩ := hx
  refine ⟨P.immersion ((Spec.map (CommRingCat.ofHom f.reducedMap.toRingHom)) z), ?_⟩
  exact congrArg (fun g : Spec Q.residueRing ⟶ Y.left => g z) f.over_X

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.OpenLift.CrystallineOpenLift
