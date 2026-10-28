import OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemeImageDominance
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Over Scheme Image -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.OverSchemeImage

noncomputable section

/-! The actual scheme-theoretic image of a morphism over a base, with
its closed inclusion and scheme-theoretically dominant factor map. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u
variable {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)

def overSchemeImage : Over S := Over.mk (f.left.imageι ≫ Y.hom)

def overSchemeImageInclusion : overSchemeImage f ⟶ Y :=
  Over.homMk f.left.imageι rfl

def overSchemeImageFactor : X ⟶ overSchemeImage f :=
  Over.homMk f.left.toImage (by
    change f.left.toImage ≫ (f.left.imageι ≫ Y.hom) = X.hom
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, f.w])

theorem overSchemeImageFactor_inclusion :
    overSchemeImageFactor f ≫ overSchemeImageInclusion f = f :=
  Over.OverMorphism.ext f.left.toImage_imageι

instance overSchemeImageInclusion_closed : IsClosedImmersion (overSchemeImageInclusion f).left :=
  inferInstanceAs (IsClosedImmersion f.left.imageι)

instance overSchemeImageInclusion_mono : Mono (overSchemeImageInclusion f) := by
  have : Mono (overSchemeImageInclusion f).left := inferInstance
  exact Over.mono_of_mono_left _

instance overSchemeImageFactor_quasiCompact [QuasiCompact f.left] :
    QuasiCompact (overSchemeImageFactor f).left :=
  inferInstanceAs (QuasiCompact f.left.toImage)

instance overSchemeImageFactor_schemeDominant [QuasiCompact f.left] :
    IsSchemeTheoreticallyDominant (overSchemeImageFactor f).left :=
  SchemeImageDominance.Construction.toImage_schemeTheoreticallyDominant f.left

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.OverSchemeImage
