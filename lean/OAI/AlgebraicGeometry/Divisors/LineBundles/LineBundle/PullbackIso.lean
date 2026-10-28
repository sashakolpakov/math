import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenRestriction

/-! # Pullback Iso -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PullbackIso.Cycles

noncomputable section

section

/-! # LineBundleCycles: actual pullback isomorphisms for algebraic line bundles -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

def lineBundlePullbackIso {X Y : Scheme.{0}} {L M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y}
    (e : L.sheaf ≅ M.sheaf) (f : X ⟶ Y) : (L.pullback f).sheaf ≅ (M.pullback f).sheaf :=
  (Scheme.Modules.pullback f).mapIso e

def lineBundlePullbackGlobalTrivialization {X Y : Scheme.{0}} {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y}
    (e : L.sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule Y) (f : X ⟶ Y) :
    (L.pullback f).sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule X :=
  (Scheme.Modules.pullback f).mapIso e ≪≫ OpenRestriction.Cycles.modulePullbackUnitIso f

def lineBundlePullbackCompIso {X Y Z : Scheme.{0}} (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((L.pullback g).pullback f).sheaf ≅ (L.pullback (f ≫ g)).sheaf :=
  (Scheme.Modules.pullbackComp f g).app L.sheaf

end

/-! Actual sheaf pullbacks transport line-bundle identifications
through a commuting square of scheme morphisms. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

def lineBundlePullbackCongrIso {X Y : Scheme.{0}} (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y)
    {f g : X ⟶ Y} (h : f = g) : (L.pullback f).sheaf ≅ (L.pullback g).sheaf := by
  subst g
  exact Iso.refl _

def lineBundlePullbackSquareIso {E D E' D' : Scheme.{0}}
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle D)
    (u : E' ⟶ E) (s : D ⟶ E) (t : D' ⟶ E') (v : D' ⟶ D)
    (h : t ≫ u = v ≫ s) (e : (L.pullback s).sheaf ≅ M.sheaf) :
    ((L.pullback u).pullback t).sheaf ≅ (M.pullback v).sheaf :=
  lineBundlePullbackCompIso L t u ≪≫ lineBundlePullbackCongrIso L h ≪≫
    (lineBundlePullbackCompIso L v s).symm ≪≫ lineBundlePullbackIso e v

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PullbackIso.Cycles
