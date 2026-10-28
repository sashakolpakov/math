/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Section Cech Indices -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.SectionCechIndices

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace

universe u

/-- Strictly increasing tuples indexing the ordered Cech complex in degree `n`. -/
def OrderedCechIndex (ι : Type u) [Preorder ι] (n : ℕ) :=
  {i : Fin (n + 1) → ι // StrictMono i}

/-- Deleting an entry from a strictly increasing tuple preserves strict increase. -/
def OrderedCechIndex.delete {ι : Type u} [Preorder ι] {n : ℕ}
    (i : OrderedCechIndex ι (n + 1)) (k : Fin (n + 2)) :
    OrderedCechIndex ι n :=
  ⟨i.1 ∘ (SimplexCategory.δ k).toOrderHom,
    i.2.comp ((SimplexCategory.δ k).toOrderHom.monotone.strictMono_of_injective
      (by
        simpa [SimplexCategory.δ] using
          (Fin.succAboveOrderEmb k).injective))⟩

@[simp]
theorem OrderedCechIndex.delete_delete {ι : Type u} [Preorder ι] {n : ℕ}
    (k : OrderedCechIndex ι (n + 1 + 1)) {i j : Fin (n + 2)} (hij : i ≤ j) :
    (k.delete j.succ).delete i = (k.delete i.castSucc).delete j := by
  apply Subtype.ext
  funext a
  have hδ := ConcreteCategory.congr_hom
    (SimplexCategory.δ_comp_δ hij)
  exact congrArg k.1 (hδ a)

/-- There are no ordered Cech indices in degrees at least the size of a finite cover. -/
theorem isEmpty_orderedCechIndex_of_card_le
    (ι : Type u) [Fintype ι] [Preorder ι] (n : ℕ) (h : Fintype.card ι ≤ n) :
    IsEmpty (OrderedCechIndex ι n) := by
  constructor
  intro i
  have hi : n + 1 ≤ Fintype.card ι := by
    simpa using Fintype.card_le_of_injective i.1 i.2.injective
  omega

/-- The formal coproduct of intersections indexed by strictly increasing tuples. -/
noncomputable def orderedCechFormalObject {X : Scheme.{u}}
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    FormalCoproduct X.Opens where
  I := OrderedCechIndex ι n
  obj i := ∏ᶜ fun k : Fin (n + 1) => U (i.1 k)

/-- Deleting one entry induces a face map between ordered intersection families. -/
noncomputable def orderedCechFace {X : Scheme.{u}}
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (n : ℕ) (k : Fin (n + 2)) :
    orderedCechFormalObject U (n + 1) ⟶ orderedCechFormalObject U n where
  f i := i.delete k
  φ i := (((FormalCoproduct.mk _ U).mapPower
    (SimplexCategory.δ k).toOrderHom.toFun).φ i.1)

theorem orderedCechFace_comp {X : Scheme.{u}}
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    {i j : Fin (n + 2)} (hij : i ≤ j) :
    orderedCechFace U (n + 1) j.succ ≫ orderedCechFace U n i =
      orderedCechFace U (n + 1) i.castSucc ≫ orderedCechFace U n j := by
  let V : FormalCoproduct X.Opens := FormalCoproduct.mk _ U
  have hmap :
      V.mapPower (SimplexCategory.δ j.succ).toOrderHom.toFun ≫
          V.mapPower (SimplexCategory.δ i).toOrderHom.toFun =
        V.mapPower (SimplexCategory.δ i.castSucc).toOrderHom.toFun ≫
          V.mapPower (SimplexCategory.δ j).toOrderHom.toFun := by
    rw [← FormalCoproduct.mapPower_comp,
      ← FormalCoproduct.mapPower_comp]
    congr 1
    exact funext (ConcreteCategory.congr_hom
      (SimplexCategory.δ_comp_δ hij))
  let hf :
      (orderedCechFace U (n + 1) j.succ ≫ orderedCechFace U n i).f =
        (orderedCechFace U (n + 1) i.castSucc ≫ orderedCechFace U n j).f :=
    funext fun k => OrderedCechIndex.delete_delete k hij
  apply FormalCoproduct.hom_ext hf
  intro k
  have hk := ((FormalCoproduct.hom_ext_iff _ _).1 hmap).2 k.1
  change
    ((V.mapPower (SimplexCategory.δ j.succ).toOrderHom.toFun ≫
          V.mapPower (SimplexCategory.δ i).toOrderHom.toFun).φ k.1 ≫
        eqToHom _) =
      (V.mapPower (SimplexCategory.δ i.castSucc).toOrderHom.toFun ≫
        V.mapPower (SimplexCategory.δ j).toOrderHom.toFun).φ k.1
  simpa only using hk

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.SectionCechIndices
