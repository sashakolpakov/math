import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdealGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.OpenRefinement

/-! # Ideal Open Matching -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdealOpenMatching

noncomputable section

/-! Effective gluing of quasi-coherent ideals on arbitrary small open covers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (C : Scheme.OpenCover.{u} X)

/-- Ideals on an open cover that agree after restriction to every common test scheme. -/
structure IdealOpenMatchingData where
  ideal : ∀ i, (C.X i).IdealSheafData
  compatible : ∀ {W : Scheme.{u}} (i j : C.I₀) (a : W ⟶ C.X i) (b : W ⟶ C.X j),
    a ≫ C.f i = b ≫ C.f j → (ideal i).comap a = (ideal j).comap b

namespace IdealOpenMatchingData

variable {C} (D : IdealOpenMatchingData C)

/-- Restrict matching ideals to the locally directed affine refinement. -/
def refinement : IdealDescent.IdealDescentData (Directed.OpenRefinement.directedOpenRefinement C) where
  ideal i := (D.ideal i.1).comap (Directed.OpenRefinement.directedOpenRefinement_toMember C i)
  compatible {i j} f := by
    let a := (Directed.OpenRefinement.directedOpenRefinement C).trans f
    let qᵢ := Directed.OpenRefinement.directedOpenRefinement_toMember C i
    let qⱼ := Directed.OpenRefinement.directedOpenRefinement_toMember C j
    have hw : (a ≫ qⱼ) ≫ C.f j.1 = qᵢ ≫ C.f i.1 := by
      rw [Category.assoc, Directed.OpenRefinement.directedOpenRefinement_toMember_map,
        Scheme.Cover.trans_map, Directed.OpenRefinement.directedOpenRefinement_toMember_map]
    exact ((D.ideal j.1).comap_comp a qⱼ).symm.trans
      (D.compatible j.1 i.1 (a ≫ qⱼ) qᵢ hw)

/-- The global ideal obtained by gluing the affine refinement. -/
def glue : X.IdealSheafData := D.refinement.gluedIdeal

/-- The glued ideal recovers every original cover member. -/
theorem glue_comap (i : C.I₀) : D.glue.comap (C.f i) = D.ideal i := by
  apply ClosedFamily.OpenEquality.ideal_eq_of_open_cover (C.X i).directedAffineCover
  intro v
  exact (D.glue.comap_comp ((C.X i).directedAffineCover.f v) (C.f i)).symm.trans
    (D.refinement.gluedIdeal_comap ⟨i, v⟩)

/-- Matching ideals on any small open cover have a unique global amalgamation. -/
theorem existsUnique_glue : ∃! I : X.IdealSheafData, ∀ i, I.comap (C.f i) = D.ideal i := by
  refine ⟨D.glue, D.glue_comap, ?_⟩
  intro I hI
  exact ClosedFamily.OpenEquality.ideal_eq_of_open_cover C I D.glue (fun i => (hI i).trans (D.glue_comap i).symm)

end IdealOpenMatchingData

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdealOpenMatching
