import Mathlib.Data.Finset.Preimage
import Mathlib.Order.Hom.WithTopBot
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.VariableEmbedding

/-! # Added Coordinate Finsets -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedCoordinateFinsets.ProjectiveCech

noncomputable section

/-! Finite faces and Čech signs after adjoining one least coordinate. -/

universe u v

variable {σ : Type u} [LinearOrder σ]

def retainedCoordinates (s : Finset σ) : Finset (WithBot σ) := s.map Function.Embedding.coeWithBot

def addedCoordinateFace (s : Finset σ) : Finset (WithBot σ) := insert ⊥ (retainedCoordinates s)

def removeAddedCoordinate (s : Finset (WithBot σ)) : Finset σ :=
  s.preimage Function.Embedding.coeWithBot Function.Embedding.coeWithBot.injective.injOn

omit [LinearOrder σ] in
theorem bot_not_mem_retainedCoordinates (s : Finset σ) : (⊥ : WithBot σ) ∉ retainedCoordinates s := by
  intro h
  obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
  exact WithBot.coe_ne_bot hi

omit [LinearOrder σ] in
theorem card_retainedCoordinates (s : Finset σ) : (retainedCoordinates s).card = s.card := Finset.card_map _

theorem card_addedCoordinateFace (s : Finset σ) : (addedCoordinateFace s).card = s.card + 1 := by
  rw [addedCoordinateFace, Finset.card_insert_of_notMem (bot_not_mem_retainedCoordinates s), card_retainedCoordinates]

theorem addedCoordinateFace_erase_bot (s : Finset σ) : (addedCoordinateFace s).erase ⊥ = retainedCoordinates s :=
  Finset.erase_insert (bot_not_mem_retainedCoordinates s)

theorem addedCoordinateFace_erase_coe (s : Finset σ) (i : σ) :
    (addedCoordinateFace s).erase (i : WithBot σ) = addedCoordinateFace (s.erase i) := by
  simp only [addedCoordinateFace, retainedCoordinates]
  rw [Finset.erase_insert_of_ne (Ne.symm WithBot.coe_ne_bot), Finset.map_erase]
  rfl

theorem retainedCoordinates_removeAddedCoordinate (s : Finset (WithBot σ)) :
    retainedCoordinates (removeAddedCoordinate s) = s.erase ⊥ := by
  apply Finset.ext
  intro i
  by_cases hi : i = ⊥
  · subst i
    simp only [bot_not_mem_retainedCoordinates, Finset.notMem_erase]
  · obtain ⟨a, rfl⟩ := WithBot.ne_bot_iff_exists.mp hi
    simp [retainedCoordinates, removeAddedCoordinate, Finset.mem_map]

theorem addedCoordinateFace_representation (s : Finset (WithBot σ)) (hs : ⊥ ∈ s) :
    addedCoordinateFace (removeAddedCoordinate s) = s := by
  rw [addedCoordinateFace, retainedCoordinates_removeAddedCoordinate, Finset.insert_erase hs]

theorem retainedCoordinates_representation (s : Finset (WithBot σ)) (hs : ⊥ ∉ s) :
    retainedCoordinates (removeAddedCoordinate s) = s := by
  rw [retainedCoordinates_removeAddedCoordinate, Finset.erase_eq_of_notMem hs]

theorem removeAddedCoordinate_addedCoordinateFace (s : Finset σ) :
    removeAddedCoordinate (addedCoordinateFace s) = s := by
  apply Finset.ext
  intro i
  simp [removeAddedCoordinate, addedCoordinateFace, retainedCoordinates, Finset.mem_map]

def addedCoordinateFaceEmbedding : Finset σ ↪ Finset (WithBot σ) where
  toFun := addedCoordinateFace
  inj' s t h := (removeAddedCoordinate_addedCoordinateFace s).symm.trans
    ((congrArg removeAddedCoordinate h).trans (removeAddedCoordinate_addedCoordinateFace t))

theorem mem_range_addedCoordinateFace (s : Finset (WithBot σ)) :
    s ∈ Set.range (addedCoordinateFaceEmbedding (σ := σ)) ↔ ⊥ ∈ s := by
  constructor
  · rintro ⟨t, rfl⟩
    exact Finset.mem_insert_self _ _
  · intro h
    exact ⟨removeAddedCoordinate s, addedCoordinateFace_representation s h⟩

theorem addedCoordinateFace_sdiff (s t : Finset σ) :
    addedCoordinateFace t \ addedCoordinateFace s = retainedCoordinates (t \ s) := by
  change insert ⊥ (retainedCoordinates t) \ insert ⊥ (retainedCoordinates s) = _
  rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem (bot_not_mem_retainedCoordinates t)]
  exact (Finset.map_sdiff t s).symm

theorem addedCoordinateFace_subset {s t : Finset σ} (h : s ⊆ t) :
    addedCoordinateFace s ⊆ addedCoordinateFace t :=
  Finset.insert_subset_insert ⊥ (Finset.map_subset_map.mpr h)

variable (R : Type v) [CommRing R]

theorem alternatingSign_added_bot (s : Finset σ) : Cech.Signs.ProjectiveCech.alternatingSign R (addedCoordinateFace s) ⊥ = 1 := by
  simp [Cech.Signs.ProjectiveCech.alternatingSign]

theorem alternatingSign_added_coe (s : Finset σ) (i : σ) :
    Cech.Signs.ProjectiveCech.alternatingSign R (addedCoordinateFace s) (i : WithBot σ) = -Cech.Signs.ProjectiveCech.alternatingSign R s i := by
  rw [addedCoordinateFace, Cech.Signs.ProjectiveCech.alternatingSign_insert_lt R (bot_not_mem_retainedCoordinates s) (WithBot.bot_lt_coe i)]
  congr 1
  exact Cech.VariableEmbedding.ProjectiveCech.alternatingSign_map R WithBot.coeOrderHom s i

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedCoordinateFinsets.ProjectiveCech
