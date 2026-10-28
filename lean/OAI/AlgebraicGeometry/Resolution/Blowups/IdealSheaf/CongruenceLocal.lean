import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CongruencePullback
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.EqualityGluing

/-! # Congruence Local -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf

noncomputable section

/-! Congruence of scheme maps can be verified on an actual open cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem CongruentMaps.Construction.IdealSheafCongruent.postcomp {U V X : Scheme.{u}} {a b : U ⟶ V} (j : V ⟶ X)
    (T : X.IdealSheafData) (h : CongruentMaps.Construction.IdealSheafCongruent a b (T.comap j)) :
    CongruentMaps.Construction.IdealSheafCongruent (a ≫ j) (b ≫ j) T := by
  constructor
  · simpa only [Scheme.IdealSheafData.comap_comp] using h.1
  · rw [Scheme.IdealSheafData.comap_comp]
    simpa only [Category.assoc] using congrArg (fun m => m ≫ j) h.2

theorem CongruentMaps.Construction.IdealSheafCongruent.of_openCover {U X : Scheme.{u}} [IsLocallyNoetherian U]
    {a b : U ⟶ X} (T : X.IdealSheafData) (C : U.OpenCover)
    (h : ∀ i, CongruentMaps.Construction.IdealSheafCongruent (C.f i ≫ a) (C.f i ≫ b) T) :
    CongruentMaps.Construction.IdealSheafCongruent a b T := by
  refine ⟨EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ C (fun i => ?_), ?_⟩
  · simpa only [Scheme.IdealSheafData.comap_comp] using (h i).1
  · let L := T.comap a
    apply Scheme.Cover.hom_ext (C.pullback₂ L.subschemeι)
    intro i
    change pullback.snd (C.f i) L.subschemeι ≫ (L.subschemeι ≫ a) =
      pullback.snd (C.f i) L.subschemeι ≫ (L.subschemeι ≫ b)
    apply (cancel_epi (L.comapIso (C.f i)).hom).mp
    simp only [← pullback.condition_assoc,
      Scheme.IdealSheafData.comapIso_hom_fst_assoc]
    have hi := (h i).2
    change (T.comap (C.f i ≫ a)).subschemeι ≫ (C.f i ≫ a) =
      (T.comap (C.f i ≫ a)).subschemeι ≫ (C.f i ≫ b) at hi
    rw [Scheme.IdealSheafData.comap_comp] at hi
    simpa only [Category.assoc] using hi

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf
