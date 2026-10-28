import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Subset Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SubsetGluing

noncomputable section

/-! Compatible open subsets on any open cover glue uniquely to an actual open subset. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem opens_eq_of_open_cover {X : Scheme.{u}} (C : X.OpenCover) (U V : X.Opens)
    (h : ∀ i, (C.f i) ⁻¹ᵁ U = (C.f i) ⁻¹ᵁ V) : U = V := by
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro x
  obtain ⟨i, y, rfl⟩ := C.exists_eq x
  exact Iff.of_eq (congrArg (fun W : (C.X i).Opens => y ∈ W) (h i))

structure OpenSubsetMatchingData {X : Scheme.{u}} (C : X.OpenCover) where
  opens : ∀ i, (C.X i).Opens
  compatible : ∀ {W : Scheme.{u}} (i j : C.I₀) (a : W ⟶ C.X i) (b : W ⟶ C.X j),
    a ≫ C.f i = b ≫ C.f j → a ⁻¹ᵁ opens i = b ⁻¹ᵁ opens j

namespace OpenSubsetMatchingData

variable {X : Scheme.{u}} {C : X.OpenCover} (D : OpenSubsetMatchingData C)

def glue : X.Opens := ⨆ i, (C.f i) ''ᵁ D.opens i

theorem glue_preimage (i : C.I₀) : (C.f i) ⁻¹ᵁ D.glue = D.opens i := by
  rw [OpenSubsetMatchingData.glue, (C.f i).preimage_iSup]
  apply le_antisymm
  · apply iSup_le
    intro j
    let a := pullback.fst (C.f i) (C.f j)
    let b := pullback.snd (C.f i) (C.f j)
    have he : a ''ᵁ b ⁻¹ᵁ D.opens j = (C.f i) ⁻¹ᵁ (C.f j) ''ᵁ D.opens j :=
      IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
        (IsPullback.of_hasPullback (C.f i) (C.f j)).flip (D.opens j)
    rw [← he, ← D.compatible i j a b pullback.condition]
    exact a.image_preimage_le (D.opens i)
  · have hi := le_iSup (fun j => (C.f i) ⁻¹ᵁ (C.f j) ''ᵁ D.opens j) i
    rw [(C.f i).preimage_image_eq] at hi
    exact hi

theorem glue_unique (U : X.Opens) (hU : ∀ i, (C.f i) ⁻¹ᵁ U = D.opens i) : U = D.glue :=
  opens_eq_of_open_cover C U D.glue (fun i => (hU i).trans (D.glue_preimage i).symm)

end OpenSubsetMatchingData

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SubsetGluing
