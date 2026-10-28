import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentSquareIsomorphisms
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentComponentIsomorphisms
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition

/-! # Descent Square Components -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentSquareComponents

noncomputable section

/-!
# Actual components of canonical square descent comparisons
-/

open _root_.CategoryTheory Opposite

universe u v u' v'

open OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition

variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (iX : X' ⟶ X) (iY : Y' ⟶ Y) (hf : iX ≫ f = f' ≫ iY)
  (P : F.obj (.mk (op Y)))

/-- The native square comparison is precisely the two standard fiber-composition comparisons. -/
theorem canonical_component :
    DescentComponentIsomorphisms.componentIso F f'
      (DescentSquareIsomorphisms.canonicalIso F f f' iX iY hf P) =
    PullbackFiberComposition.fiberIsoTo F f P iX (f' ≫ iY) hf ≪≫ (PullbackFiberComposition.fiberIso F iY P f').symm := by
  apply Iso.ext
  change ((Cat.Hom.toNatIso (F.isoMapOfCommSq (CommSq.mk hf).op.toLoc)).symm.app P).hom = _
  rw [F.isoMapOfCommSq_eq _ (f' ≫ iY).op.toLoc rfl]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentSquareComponents
