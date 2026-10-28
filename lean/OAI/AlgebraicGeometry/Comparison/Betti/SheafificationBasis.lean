import Mathlib

/-! # Sheafification Basis -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SheafificationBasis

noncomputable section

/-! An isomorphism on a basis of opens induces an isomorphism after sheafification. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} {F G : X.Presheaf AddCommGrpCat.{0}}
  (a : F ⟶ G) {B : Set (Opens X)} (hB : Opens.IsBasis B)
  (ha : ∀ U ∈ B, IsIso (a.app (op U)))

include hB ha

theorem stalk_bijective (x : X) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map a) := by
  constructor
  · exact TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis hB
      (fun U hU => by
        have := ha U hU
        exact (ConcreteCategory.bijective_of_isIso (a.app (op U))).injective) x
  · intro t
    obtain ⟨U, hxU, hU, s, hs⟩ := TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hB G x t
    have : IsIso (a.app (op U)) := ha U hU
    obtain ⟨r, hr⟩ := (ConcreteCategory.bijective_of_isIso (a.app (op U))).surjective s
    refine ⟨F.germ U x hxU r, ?_⟩
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hr]
    exact hs

theorem stalk_isIso (x : X) : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map a) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (stalk_bijective a hB ha x)

theorem sheafifyMap_stalk_isIso (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (sheafifyMap (Opens.grothendieckTopology X) a)) := by
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x
  let J := Opens.grothendieckTopology X
  have : IsIso (T.map a) := stalk_isIso a hB ha x
  have : IsIso (T.map (toSheafify J F)) := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x _ F
  have : IsIso (T.map (toSheafify J G)) := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x _ G
  have he : T.map a ≫ T.map (toSheafify J G) =
      T.map (toSheafify J F) ≫ T.map (sheafifyMap J a) := by
    rw [← T.map_comp, ← T.map_comp, toSheafify_naturality]
  have hi : IsIso (T.map (toSheafify J F) ≫ T.map (sheafifyMap J a)) := by
    rw [← he]
    infer_instance
  exact (isIso_comp_left_iff (T.map (toSheafify J F)) (T.map (sheafifyMap J a))).mp hi

theorem map_isIso : IsIso ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map a) := by
  have : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (sheafifyMap (Opens.grothendieckTopology X) a)) := sheafifyMap_stalk_isIso a hB ha
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
    ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map a)

end

end OAI.AlgebraicGeometry.Comparison.Betti.SheafificationBasis
