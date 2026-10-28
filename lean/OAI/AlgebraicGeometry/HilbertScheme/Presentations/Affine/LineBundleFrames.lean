import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Classification
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison
import Mathlib.RingTheory.PicardGroup

/-! # Line Bundle Frames -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.LineBundleFrames

noncomputable section

/-! Line bundles on an affine scheme with trivial ring Picard group
have actual global frames. In particular this applies to polynomial charts
over a field, since their coordinate rings are unique factorization domains. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R : CommRingCat.{u}} [Subsingleton (CommRing.Pic R)]

def affineLineBundleFrame (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Spec R)) :
    L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec R) := by
  let L' := Picard.PoincareBundle.Line.Comparison.Bundle.fromShared L
  let M := (moduleSpecΓFunctor (R := R)).obj L'.sheaf
  let : Module.Invertible R M := Picard.PoincareBundle.Affine.Classification.globalSections_invertible L'
  let : Module.Free R M := inferInstance
  let e : M ≃ₗ[R] R := (Module.Invertible.free_iff_linearEquiv.mp inferInstance).some
  exact (Picard.PoincareBundle.QuasiCoherent.affineTildeIso L').symm ≪≫
    (tilde.functor R).mapIso e.toModuleIso ≪≫ tildeSelf

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.LineBundleFrames
