import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyOpenGluing
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.Over

/-! # Family Cover Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyCoverSheaf

noncomputable section

/-! The sheaf condition for embedded flat families on the presieve of an open base cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (P T : Over S) (C : Scheme.OpenCover.{u} T.left)

/-- Embedded flat families satisfy the sheaf condition on every small open base cover. -/
theorem embeddedFlatFamily_isSheafFor_cover :
    Presieve.IsSheafFor (FamilyFunctor.embeddedFlatFamilyFunctor P)
      (Presieve.ofArrows (FamilyOpenCover.overOpenCoverObject T C) (FamilyOpenCover.overOpenCoverMap T C)) := by
  apply (Presieve.isSheafFor_arrows_iff (FamilyFunctor.embeddedFlatFamilyFunctor P) (FamilyOpenCover.overOpenCoverMap T C)).mpr
  intro F hF
  let D : FamilyMatching.EmbeddedFamilyMatchingData P T C :=
    { family := F
      compatible i j f h w := hF i j _ f h w }
  exact D.existsUnique_glue

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyCoverSheaf
