import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdealOpenMatching
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyOpenCover

/-! # Ideal Matching -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.IdealMatching

noncomputable section

/-! Matching ideals can be checked using morphisms over the original base scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def overIdealOpenMatchingData {S : Scheme.{u}} (M : Over S) (C : M.left.OpenCover)
    (I : ∀ i, (C.X i).IdealSheafData)
    (hI : ∀ {T : Over S} (i j : C.I₀)
      (a : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject M C i) (b : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject M C j),
      a ≫ Embedded.FamilyOpenCover.overOpenCoverMap M C i = b ≫ Embedded.FamilyOpenCover.overOpenCoverMap M C j →
        (I i).comap a.left = (I j).comap b.left) : IdealOpenMatching.IdealOpenMatchingData C where
  ideal := I
  compatible {W} i j a b h := by
    let T : Over S := Over.mk (a ≫ (C.f i ≫ M.hom))
    let a' : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject M C i := Over.homMk a rfl
    let b' : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject M C j := Over.homMk b (by
      change b ≫ (C.f j ≫ M.hom) = a ≫ (C.f i ≫ M.hom)
      rw [← Category.assoc, ← Category.assoc, h])
    exact hI i j a' b' (Over.OverMorphism.ext h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.IdealMatching
