import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SubsetGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyOpenCover

/-! # Open Subset Matching -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.OpenSubsetMatching

noncomputable section

/-! Matching open subsets may be checked using morphisms over the original base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def overOpenSubsetMatchingData {S : Scheme.{u}} (M : Over S) (C : M.left.OpenCover)
    (U : ∀ i, (C.X i).Opens)
    (hU : ∀ {T : Over S} (i j : C.I₀)
      (a : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject M C i) (b : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject M C j),
      a ≫ Embedded.FamilyOpenCover.overOpenCoverMap M C i = b ≫ Embedded.FamilyOpenCover.overOpenCoverMap M C j →
        a.left ⁻¹ᵁ U i = b.left ⁻¹ᵁ U j) : Open.SubsetGluing.OpenSubsetMatchingData C where
  opens := U
  compatible {W} i j a b h := by
    let T : Over S := Over.mk (a ≫ (C.f i ≫ M.hom))
    let a' : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject M C i := Over.homMk a rfl
    let b' : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject M C j := Over.homMk b (by
      change b ≫ (C.f j ≫ M.hom) = a ≫ (C.f i ≫ M.hom)
      rw [← Category.assoc, ← Category.assoc, h])
    exact hU i j a' b' (Over.OverMorphism.ext h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.OpenSubsetMatching
