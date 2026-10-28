import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CongruenceLocal
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlledIdealKernel

/-! # Congruence Support -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf

noncomputable section

/-! It suffices to check intrinsic congruence on open neighborhoods of the two pulled-back supports. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem CongruentMaps.Construction.IdealSheafCongruent.of_comap_top {U X : Scheme.{u}} (a b : U ⟶ X) (T : X.IdealSheafData)
    (ha : T.comap a = ⊤) (hb : T.comap b = ⊤) : CongruentMaps.Construction.IdealSheafCongruent a b T := by
  refine ⟨ha.trans hb.symm, ?_⟩
  let : IsEmpty (T.comap a).subscheme := ⟨fun x => by
    have hrange : Set.range (T.comap a).subschemeι = (∅ : Set U) := by
      rw [Scheme.IdealSheafData.range_subschemeι, ha, Scheme.IdealSheafData.support_top]
      rfl
    have hx : (T.comap a).subschemeι x ∈ (∅ : Set U) := by
      rw [← hrange]
      exact ⟨x, rfl⟩
    exact hx⟩
  exact isInitialOfIsEmpty.hom_ext _ _

theorem CongruentMaps.Construction.IdealSheafCongruent.of_neighborhoods {U X : Scheme.{u}} [IsLocallyNoetherian U]
    (a b : U ⟶ X) (T : X.IdealSheafData)
    (h : ∀ x : U, ∃ (V : Scheme.{u}) (j : V ⟶ U),
      IsOpenImmersion j ∧ x ∈ Set.range j ∧ CongruentMaps.Construction.IdealSheafCongruent (j ≫ a) (j ≫ b) T) :
    CongruentMaps.Construction.IdealSheafCongruent a b T := by
  classical
  choose V j hj hx hc using h
  let C : U.OpenCover := Scheme.Cover.mkOfCovers U V j (fun x => ⟨x, hx x⟩) hj
  exact CongruentMaps.Construction.IdealSheafCongruent.of_openCover T C hc

theorem CongruentMaps.Construction.IdealSheafCongruent.of_support_neighborhoods {U X : Scheme.{u}} [IsLocallyNoetherian U]
    (a b : U ⟶ X) (T : X.IdealSheafData)
    (h : ∀ x : U, x ∈ (T.comap a).support ∨ x ∈ (T.comap b).support →
      ∃ (V : Scheme.{u}) (j : V ⟶ U),
        IsOpenImmersion j ∧ x ∈ Set.range j ∧ CongruentMaps.Construction.IdealSheafCongruent (j ≫ a) (j ≫ b) T) :
    CongruentMaps.Construction.IdealSheafCongruent a b T := by
  classical
  apply CongruentMaps.Construction.IdealSheafCongruent.of_neighborhoods a b T
  intro x
  by_cases hx : x ∈ (T.comap a).support ∨ x ∈ (T.comap b).support
  · exact h x hx
  · let W : U.Opens := (T.comap a).support.compl ⊓ (T.comap b).support.compl
    have hxW : x ∈ W := ⟨fun ha => hx (Or.inl ha), fun hb => hx (Or.inr hb)⟩
    refine ⟨W, W.ι, inferInstance, ⟨⟨x, hxW⟩, rfl⟩, CongruentMaps.Construction.IdealSheafCongruent.of_comap_top _ _ T ?_ ?_⟩
    · rw [Scheme.IdealSheafData.comap_comp]
      exact ControlledIdealKernel.Construction.idealSheaf_comap_eq_top_of_avoids_support (T.comap a) W.ι (fun y => y.property.1)
    · rw [Scheme.IdealSheafData.comap_comp]
      exact ControlledIdealKernel.Construction.idealSheaf_comap_eq_top_of_avoids_support (T.comap b) W.ι (fun y => y.property.2)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf
