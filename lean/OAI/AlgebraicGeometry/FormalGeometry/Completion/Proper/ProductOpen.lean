import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.AffineBaseChange

/-! # Product Open -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ProductOpen.Construction

noncomputable section

/-!
# Completion: restriction of the product and its section to a base open
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {S X Y : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (U : Y.Opens)

/-- Inclusion of the product with a base open into the original product. -/
def properProductOpenMap : pullback p (U.ι ≫ q) ⟶ pullback p q :=
  pullback.lift (pullback.fst p (U.ι ≫ q)) (pullback.snd p (U.ι ≫ q) ≫ U.ι)
    (by rw [Category.assoc]; exact pullback.condition)

@[reassoc (attr := simp)]
theorem properProductOpenMap_fst : properProductOpenMap p q U ≫ pullback.fst p q =
    pullback.fst p (U.ι ≫ q) := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem properProductOpenMap_snd : properProductOpenMap p q U ≫ pullback.snd p q =
    pullback.snd p (U.ι ≫ q) ≫ U.ι := pullback.lift_snd _ _ _

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of K)) (q : Y ⟶ Spec (CommRingCat.of K)) (U : Y.Opens)

/-- The product section commutes with restriction of the base to an open. -/
theorem properProductSection_open (e : Spec (CommRingCat.of K) ⟶ X)
    (he : e ≫ p = 𝟙 _) :
    AffineBaseChange.Construction.properProductSection p (U.ι ≫ q) e he ≫ properProductOpenMap p q U =
      U.ι ≫ AffineBaseChange.Construction.properProductSection p q e he := by
  apply pullback.hom_ext <;> simp [AffineBaseChange.Construction.properProductSection, Category.assoc]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ProductOpen.Construction
