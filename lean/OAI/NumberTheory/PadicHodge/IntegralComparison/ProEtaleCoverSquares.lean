import OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtalePullbackSections

/-! # Pro Etale Cover Squares -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtaleCoverSquares

noncomputable section

/-! Actual commutative squares of schemes give maps to the base-changed
objects of the pro-étale site, compatibly with cover projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def map {U : X.ProEt} {V : Y.ProEt} (g : U.left ⟶ V.left)
    (h : g ≫ V.hom = U.hom ≫ f) : U ⟶ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).obj V :=
  MorphismProperty.Over.homMk (pullback.lift g U.hom h) (pullback.lift_snd _ _ _)

@[reassoc (attr := simp)] theorem map_fst {U : X.ProEt} {V : Y.ProEt}
    (g : U.left ⟶ V.left) (h : g ≫ V.hom = U.hom ≫ f) :
    (ProEtaleCoverSquares.map f g h).left ≫ pullback.fst V.hom f = g := pullback.lift_fst _ _ _

theorem naturality {U D : Y.ProEt} {V E : X.ProEt} (a : D ⟶ U) (c : E ⟶ V)
    (gU : V.left ⟶ U.left) (gD : E.left ⟶ D.left)
    (hU : gU ≫ U.hom = V.hom ≫ f) (hD : gD ≫ D.hom = E.hom ≫ f)
    (h : gD ≫ a.left = c.left ≫ gU) :
    ProEtaleCoverSquares.map f gD hD ≫ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).map a = c ≫ ProEtaleCoverSquares.map f gU hU := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · have he : ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).map a).left ≫ pullback.fst U.hom f =
        pullback.fst D.hom f ≫ a.left := (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChangeProjection f).naturality a
    change ((ProEtaleCoverSquares.map f gD hD).left ≫ ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).map a).left) ≫ pullback.fst U.hom f =
      (c.left ≫ (ProEtaleCoverSquares.map f gU hU).left) ≫ pullback.fst U.hom f
    rw [Category.assoc, he, ← Category.assoc, map_fst, Category.assoc, map_fst, h]
  · exact (MorphismProperty.Over.w (ProEtaleCoverSquares.map f gD hD ≫ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).map a)).trans
      (MorphismProperty.Over.w (c ≫ ProEtaleCoverSquares.map f gU hU)).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtaleCoverSquares
