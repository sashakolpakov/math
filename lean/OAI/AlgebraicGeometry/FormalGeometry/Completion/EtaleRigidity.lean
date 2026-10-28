import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Topology.Connected.Clopen

/-! # Etale Rigidity -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.EtaleRigidity.Construction

noncomputable section

/-!
# Completion: uniqueness of lifts to a separated étale scheme

The equalizer of two maps over the base is both open and closed. On a
connected source, agreement after any map from a nonempty scheme therefore
forces equality everywhere. The agreement is equality of scheme maps.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- The equalizer of two maps into an étale scheme over the base is open. -/
theorem etale_equalizer_isOpenImmersion {S : Scheme.{u}} {X Y : Over S}
    [Etale Y.hom] (f g : X ⟶ Y) : IsOpenImmersion (equalizer.ι f g).left := by
  refine MorphismProperty.of_isPullback
    ((Limits.isPullback_equalizer_prod f g).map (Over.forget _)).flip ?_
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _
    (Over.prodLeftIsoPullback Y Y).hom]
  convert! (inferInstance : IsOpenImmersion (pullback.diagonal Y.hom))
  ext1 <;> simp [← Over.comp_left]

/-- A map into a separated étale scheme is determined by its restriction to any nonempty
test scheme when its source is connected. -/
theorem etale_hom_ext_of_nonempty {S : Scheme.{u}} {X Y W : Over S}
    [PreconnectedSpace X.left] [Nonempty W.left] [Etale Y.hom] [IsSeparated Y.hom]
    (f g : X ⟶ Y) (a : W ⟶ X) (h : a ≫ f = a ≫ g) : f = g := by
  have : IsOpenImmersion (equalizer.ι f g).left := etale_equalizer_isOpenImmersion f g
  have hc : IsClopen (Set.range (equalizer.ι f g).left) :=
    ⟨(Scheme.Hom.isClosedEmbedding _).isClosed_range,
      (equalizer.ι f g).left.isOpenEmbedding.isOpen_range⟩
  have hn : (Set.range (equalizer.ι f g).left).Nonempty :=
    ⟨_, ⟨(equalizer.lift a h).left (Nonempty.some inferInstance), rfl⟩⟩
  have : Surjective (equalizer.ι f g).left :=
    ⟨Set.range_eq_univ.mp (hc.eq_univ hn)⟩
  have : IsIso (equalizer.ι f g).left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  apply Over.OverMorphism.ext
  rw [← cancel_epi (equalizer.ι f g).left]
  exact congrArg (fun k => k.left) (equalizer.condition f g)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.EtaleRigidity.Construction
