import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.DescentUniqueness

/-! # Faithful Line Morphisms -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FaithfulLineMorphisms

noncomputable section

/-! Faithfully flat affine pullback detects equality of morphisms into a
line bundle. This uses the proved invariant-sheaf unit isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Comonad

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [IsAffineHom f] [Flat f] [Surjective f] [IsLocallyNoetherian Y]

theorem line_pullback_unit_mono (N : Y.Modules) (hN : PoincareBundle.Line.Bundles.IsLine N) :
    Mono ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let cadj := ComonadicityInternal.comparisonAdjunction adj
  let D := (Comonad.comparison adj).obj N
  let i := PoincareBundle.BeckDescent.invariantSheafInclusion f D
  have hi : Mono i := inferInstanceAs (Mono (equalizer.ι _ _))
  let e := PoincareBundle.Line.DescentUniqueness.unitIso f N hN
  have he : cadj.unit.app N ≫ i = adj.unit.app N := by
    change equalizer.lift (adj.homEquiv _ _ (𝟙 _)) _ ≫ equalizer.ι _ _ = adj.unit.app N
    rw [equalizer.lift_ι, Adjunction.homEquiv_unit]
    simp
  have he' : e.hom ≫ i = adj.unit.app N := he
  have hm : Mono (e.hom ≫ i) := inferInstance
  exact he' ▸ hm

theorem pullbackHom_injective_of_lineTarget (M N : Y.Modules)
    (hN : PoincareBundle.Line.Bundles.IsLine N) :
    Function.Injective ((Scheme.Modules.pullback f).map : (M ⟶ N) → _) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have : Mono (adj.unit.app N) := line_pullback_unit_mono f N hN
  intro a b hab
  apply (cancel_mono (adj.unit.app N)).mp
  exact (adj.unit.naturality a).trans
    ((congrArg (fun t => adj.unit.app M ≫ (Scheme.Modules.pushforward f).map t) hab).trans
      (adj.unit.naturality b).symm)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FaithfulLineMorphisms
