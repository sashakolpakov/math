import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.TargetBaseChangeIsomorphism
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.LocalClosedFiberIsomorphism
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.TargetFlatProjection
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Fiber Isomorphism At Target -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.FiberIsomorphismAtTarget

noncomputable section

/-! If the source is flat over the parameter base, isomorphism of a
finite morphism on a coefficient fiber gives isomorphism over each target local spectrum in that fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y B : Scheme.{u}} [IsLocallyNoetherian Y]
variable (f : X ⟶ Y) (q : Y ⟶ B) [IsFinite f] [Flat (f ≫ q)]

theorem finite_isIso_at_target_of_fiber (y : Y)
    (h : IsIso (Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q (B.fromSpecResidueField (q y)))) :
    IsIso (pullback.fst (Y.fromSpecStalk y) f) := by
  let R : Type u := B.presheaf.stalk (q y)
  let A : Type u := Y.presheaf.stalk y
  let hR : IsLocalRing R := inferInstanceAs (IsLocalRing (B.presheaf.stalk (q y)))
  let hA : IsLocalRing A := inferInstanceAs (IsLocalRing (Y.presheaf.stalk y))
  let hN : IsNoetherianRing A := inferInstanceAs (IsNoetherianRing (Y.presheaf.stalk y))
  let : Algebra R A := (q.stalkMap y).hom.toAlgebra
  let : IsLocalHom (algebraMap R A) := inferInstanceAs (IsLocalHom (q.stalkMap y).hom)
  let p := pullback.fst (Y.fromSpecStalk y) f
  let q' : Spec (.of A) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let b := B.fromSpecStalk (q y)
  let c := Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))
  let : Flat (p ≫ q') := Local.TargetFlatProjection.localTargetOverBaseStalkMap_flat f q y
  apply @LocalClosedFiberIsomorphism.finiteLocal_isIso_of_closedFiber R A _ hR _ hA hN _ _ _ p _ _
  have hab : Y.fromSpecStalk y ≫ q = q' ≫ b := (Scheme.SpecMap_stalkMap_fromSpecStalk q).symm
  have hc : IsIso (Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q (c ≫ b)) := h
  exact Relative.TargetBaseChangeIsomorphism.relativeMorphismBaseChange_target_square f q (Y.fromSpecStalk y) q' b hab c hc

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.FiberIsomorphismAtTarget
