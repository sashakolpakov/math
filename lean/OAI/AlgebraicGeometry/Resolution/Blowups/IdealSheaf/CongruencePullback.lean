import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CongruentMaps

/-! # Congruence Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf

noncomputable section

/-! Intrinsic congruence persists under domain refinement and identifies every point on the comparison subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem CongruentMaps.Construction.IdealSheafCongruent.symm {U X : Scheme.{u}} {a b : U ⟶ X} {T : X.IdealSheafData}
    (h : CongruentMaps.Construction.IdealSheafCongruent a b T) : CongruentMaps.Construction.IdealSheafCongruent b a T := by
  refine ⟨h.1.symm, ?_⟩
  rw [← h.1]
  exact h.2.symm

theorem CongruentMaps.Construction.IdealSheafCongruent.comp {V U X : Scheme.{u}} {a b : U ⟶ X} {T : X.IdealSheafData}
    (h : CongruentMaps.Construction.IdealSheafCongruent a b T) (q : V ⟶ U) : CongruentMaps.Construction.IdealSheafCongruent (q ≫ a) (q ≫ b) T := by
  constructor
  · rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, h.1]
  · rw [Scheme.IdealSheafData.comap_comp]
    let L := T.comap a
    let r := Scheme.IdealSheafData.subschemeMap (L.comap q) L q (L.le_map_comap q)
    have he : r ≫ L.subschemeι = (L.comap q).subschemeι ≫ q :=
      Scheme.IdealSheafData.subschemeMap_subschemeι (L.comap q) L q (L.le_map_comap q)
    change (L.comap q).subschemeι ≫ (q ≫ a) = (L.comap q).subschemeι ≫ (q ≫ b)
    calc
      _ = (r ≫ L.subschemeι) ≫ a := by rw [he, Category.assoc]
      _ = r ≫ (L.subschemeι ≫ a) := Category.assoc _ _ _
      _ = r ≫ (L.subschemeι ≫ b) := congrArg (fun m => r ≫ m) h.2
      _ = (L.comap q).subschemeι ≫ (q ≫ b) := by rw [← Category.assoc, he, Category.assoc]

theorem CongruentMaps.Construction.IdealSheafCongruent.point_eq_on_support {U X : Scheme.{u}} {a b : U ⟶ X} {T : X.IdealSheafData}
    (h : CongruentMaps.Construction.IdealSheafCongruent a b T) (x : U) (hx : x ∈ (T.comap a).support) : a x = b x := by
  have hrange : x ∈ Set.range (T.comap a).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hx
  obtain ⟨y, rfl⟩ := hrange
  exact congrArg (fun f => f y) h.2

theorem CongruentMaps.Construction.IdealSheafCongruent.of_comp_mono {U V X : Scheme.{u}} {a b : U ⟶ V} (j : V ⟶ X) [Mono j]
    (T : X.IdealSheafData) (h : CongruentMaps.Construction.IdealSheafCongruent (a ≫ j) (b ≫ j) T) :
    CongruentMaps.Construction.IdealSheafCongruent a b (T.comap j) := by
  have hT : (T.comap j).comap a = (T.comap j).comap b := by
    simpa only [Scheme.IdealSheafData.comap_comp] using h.1
  refine ⟨hT, ?_⟩
  rw [← Scheme.IdealSheafData.comap_comp]
  apply (cancel_mono j).mp
  simpa only [Category.assoc] using h.2

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf
