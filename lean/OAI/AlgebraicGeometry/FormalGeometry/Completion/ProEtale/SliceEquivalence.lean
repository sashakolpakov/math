import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.Slice
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.SingleCover

/-! # Slice Equivalence -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.SliceEquivalence.Construction

noncomputable section

/-!
# Completion: the actual site over a weakly étale object equals the slice site

A morphism between weakly étale objects is weakly étale. Consequently
every object of the slice comes from the smaller pro-étale site.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} (U : X.ProEt)

/-- Recover the weakly étale morphism to the covering scheme from a slice object. -/
def proEtaleFromSlice : Over U ⥤ U.left.ProEt where
  obj V :=
    have := SingleCover.Construction.proEtaleMorphism_weaklyEtale V.hom
    Scheme.ProEt.mk V.hom.left
  map g := MorphismProperty.Over.homMk g.left.left
    (congrArg (fun k => k.left) g.w)

/-- The actual equivalence with the slice category of the original site. -/
def proEtaleSliceEquivalence : U.left.ProEt ≌ Over U where
  functor := Slice.Construction.proEtaleToSlice U
  inverse := proEtaleFromSlice U
  unitIso := NatIso.ofComponents
    (fun V => MorphismProperty.Over.isoMk (Iso.refl V.left) (by simp [proEtaleFromSlice, Slice.Construction.proEtaleToSlice]))
    (by
      intro V W g
      apply MorphismProperty.Over.Hom.ext
      change g.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left
      simp)
  counitIso := NatIso.ofComponents
    (fun V => Over.isoMk
      (MorphismProperty.Over.isoMk (Iso.refl V.left.left) (by
        simp [Slice.Construction.proEtaleToSlice, proEtaleFromSlice]))
      (by
        apply MorphismProperty.Over.Hom.ext
        change 𝟙 _ ≫ V.hom.left = V.hom.left
        simp))
    (by
      intro V W g
      apply Over.OverMorphism.ext
      apply MorphismProperty.Over.Hom.ext
      change g.left.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left.left
      simp)
  functor_unitIso_comp V := by
    apply Over.OverMorphism.ext
    apply MorphismProperty.Over.Hom.ext
    change 𝟙 V.left ≫ 𝟙 V.left = 𝟙 V.left
    simp

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.SliceEquivalence.Construction
