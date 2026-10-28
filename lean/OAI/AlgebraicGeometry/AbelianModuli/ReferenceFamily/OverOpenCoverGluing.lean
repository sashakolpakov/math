import Mathlib.AlgebraicGeometry.Gluing

/-! # Over Open Cover Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OverOpenCoverGluing

noncomputable section

/-! Compatible actual scheme maps over a fixed base glue to a map
over that same base, with exact restrictions and uniqueness. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {B : Scheme} (X Y : Over B) (U : X.left.OpenCover)
    (f : ∀ i : U.I₀, U.X i ⟶ Y.left)
    (hw : ∀ i, f i ≫ Y.hom = U.f i ≫ X.hom)
    (hf : ∀ i j, pullback.fst (U.f i) (U.f j) ≫ f i = pullback.snd _ _ ≫ f j)

def glueOverOpenCover : X ⟶ Y :=
  Over.homMk (U.glueMorphisms f hf) (by
    apply U.hom_ext
    intro i
    rw [← Category.assoc, U.ι_glueMorphisms, hw])

theorem glueOverOpenCover_fac (i : U.I₀) : U.f i ≫ (glueOverOpenCover X Y U f hw hf).left = f i :=
  U.ι_glueMorphisms f hf i

theorem glueOverOpenCover_unique (g : X ⟶ Y) (hg : ∀ i, U.f i ≫ g.left = f i) :
    g = glueOverOpenCover X Y U f hw hf := by
  apply Over.OverMorphism.ext
  apply U.hom_ext
  intro i
  exact (hg i).trans (glueOverOpenCover_fac X Y U f hw hf i).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OverOpenCoverGluing
