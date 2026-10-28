import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Fiber Points -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.FiberPoints

noncomputable section

/-! Closed points in finite fibers and uniqueness of rational points
in a scheme fiber product from their two projections. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem closed {X Y : Scheme} (f : X ⟶ Y) [LocallyQuasiFinite f]
    [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({f x} : Set _)) : IsClosed ({x} : Set _) := by
  let : IsClosedImmersion (Y.fromSpecResidueField (f x)) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hi : IsClosedImmersion (f.fiberι (f x)) :=
    MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance
  let := hi
  have hs := (f.quasiFiniteAt x).isClopen_singleton_asFiber.isClosed
  simpa only [Set.image_singleton, Scheme.Hom.fiberι_asFiber] using
    (f.fiberι (f x)).isClosedEmbedding.isClosedMap _ hs

theorem pullback_ext {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)
    (t : S ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType (f ≫ t)] [LocallyOfFiniteType (g ≫ t)]
    [LocallyOfFiniteType (pullback.fst f g ≫ f ≫ t)]
    (z w : ↥(pullback f g)) (hz : IsClosed ({z} : Set _)) (hw : IsClosed ({w} : Set _))
    (hfst : pullback.fst f g z = pullback.fst f g w)
    (hsnd : pullback.snd f g z = pullback.snd f g w) : z = w := by
  let F := pullback.fst f g ≫ f ≫ t
  let p := pointOfClosedPoint F z hz
  let q := pointOfClosedPoint F w hw
  have hp : p ≫ F = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  have hq : q ≫ F = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  have hpx : (p ≫ pullback.fst f g) ≫ (f ≫ t) = 𝟙 _ := by simpa [F] using hp
  have hqx : (q ≫ pullback.fst f g) ≫ (f ≫ t) = 𝟙 _ := by simpa [F] using hq
  have hpy : (p ≫ pullback.snd f g) ≫ (g ≫ t) = 𝟙 _ := by
    rw [Category.assoc, ← Category.assoc (pullback.snd f g), ← pullback.condition, Category.assoc]
    exact hp
  have hqy : (q ≫ pullback.snd f g) ≫ (g ≫ t) = 𝟙 _ := by
    rw [Category.assoc, ← Category.assoc (pullback.snd f g), ← pullback.condition, Category.assoc]
    exact hq
  have he : p = q := by
    apply pullback.hom_ext
    · apply ext_of_apply_closedPoint_eq (f ≫ t) hpx hqx
      simpa only [Scheme.Hom.comp_apply, p, q, pointOfClosedPoint_apply] using hfst
    · apply ext_of_apply_closedPoint_eq (g ≫ t) hpy hqy
      simpa only [Scheme.Hom.comp_apply, p, q, pointOfClosedPoint_apply] using hsnd
  have he' := congrArg (fun a => a (IsLocalRing.closedPoint ℂ)) he
  simpa only [p, q, pointOfClosedPoint_apply] using he'

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.FiberPoints
