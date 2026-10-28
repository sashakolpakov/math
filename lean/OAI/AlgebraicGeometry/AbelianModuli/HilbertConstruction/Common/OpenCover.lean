import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyOpenCover

/-! # Open Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.OpenCover

noncomputable section

/-! A common open refinement, with both projection maps over the original base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) (C D : M.left.OpenCover)

def commonOpenCover : M.left.OpenCover :=
  C.bind (fun i => D.pullback₁ (C.f i))

def commonOpenCoverLeft (i : C.I₀) (j : D.I₀) :
    Embedded.FamilyOpenCover.overOpenCoverObject M (commonOpenCover M C D) ⟨i, j⟩ ⟶ Embedded.FamilyOpenCover.overOpenCoverObject M C i :=
  Over.homMk (pullback.fst (C.f i) (D.f j)) (by
    change pullback.fst (C.f i) (D.f j) ≫ (C.f i ≫ M.hom) =
      (pullback.fst (C.f i) (D.f j) ≫ C.f i) ≫ M.hom
    exact (Category.assoc _ _ _).symm)

def commonOpenCoverRight (i : C.I₀) (j : D.I₀) :
    Embedded.FamilyOpenCover.overOpenCoverObject M (commonOpenCover M C D) ⟨i, j⟩ ⟶ Embedded.FamilyOpenCover.overOpenCoverObject M D j :=
  Over.homMk (pullback.snd (C.f i) (D.f j)) (by
    change pullback.snd (C.f i) (D.f j) ≫ (D.f j ≫ M.hom) =
      (pullback.fst (C.f i) (D.f j) ≫ C.f i) ≫ M.hom
    rw [← Category.assoc, pullback.condition])

theorem commonOpenCoverLeft_map (i : C.I₀) (j : D.I₀) :
    commonOpenCoverLeft M C D i j ≫ Embedded.FamilyOpenCover.overOpenCoverMap M C i =
      Embedded.FamilyOpenCover.overOpenCoverMap M (commonOpenCover M C D) ⟨i, j⟩ := by
  apply Over.OverMorphism.ext
  rfl

theorem commonOpenCoverRight_map (i : C.I₀) (j : D.I₀) :
    commonOpenCoverRight M C D i j ≫ Embedded.FamilyOpenCover.overOpenCoverMap M D j =
      Embedded.FamilyOpenCover.overOpenCoverMap M (commonOpenCover M C D) ⟨i, j⟩ := by
  apply Over.OverMorphism.ext
  exact pullback.condition.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.OpenCover
