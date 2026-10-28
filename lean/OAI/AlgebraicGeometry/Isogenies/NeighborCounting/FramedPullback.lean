import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PullbackUnitCoherence

/-! # Framed Pullback -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback

noncomputable section

/-! Morphism coordinates under iterated native pullback and equal
composite scheme morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PullbackUnitCoherence

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable {M N : Z.Modules}

theorem pullbackFrame_comp (eM : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Z) :
    FramedHom.pullbackFrame f (FramedHom.pullbackFrame g eM) =
      (Scheme.Modules.pullbackComp f g).app M ≪≫ FramedHom.pullbackFrame (f ≫ g) eM := by
  apply Iso.ext
  let Lf := Scheme.Modules.pullback f
  let Lg := Scheme.Modules.pullback g
  let L := Scheme.Modules.pullback (f ≫ g)
  let c := Scheme.Modules.pullbackComp f g
  change Lf.map (Lg.map eM.hom ≫ (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso g).hom) ≫
      (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso f).hom =
    c.hom.app M ≫ (L.map eM.hom ≫ (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso (f ≫ g)).hom)
  rw [Lf.map_comp, Category.assoc, ← PullbackUnitCoherence.pullbackStructureSheafIso_comp]
  change (Lg ⋙ Lf).map eM.hom ≫
    (c.hom.app (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Z) ≫ (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso (f ≫ g)).hom) = _
  rw [← Category.assoc, c.hom.naturality, Category.assoc]

def pullbackHomTo (p : X ⟶ Z) (h : f ≫ g = p)
    (q : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N) :
    (Scheme.Modules.pullback p).obj M ⟶ (Scheme.Modules.pullback p).obj N :=
  ((Scheme.Modules.pullbackComp f g ≪≫ Scheme.Modules.pullbackCongr h).app M).inv ≫
    (Scheme.Modules.pullback f).map q ≫
      ((Scheme.Modules.pullbackComp f g ≪≫ Scheme.Modules.pullbackCongr h).app N).hom

def pullbackIsoTo (p : X ⟶ Z) (h : f ≫ g = p)
    (e : (Scheme.Modules.pullback g).obj M ≅ (Scheme.Modules.pullback g).obj N) :
    (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback p).obj N :=
  ((Scheme.Modules.pullbackComp f g ≪≫ Scheme.Modules.pullbackCongr h).app M).symm ≪≫
    (Scheme.Modules.pullback f).mapIso e ≪≫
      ((Scheme.Modules.pullbackComp f g ≪≫ Scheme.Modules.pullbackCongr h).app N)

theorem pullbackIsoTo_hom (p : X ⟶ Z) (h : f ≫ g = p)
    (e : (Scheme.Modules.pullback g).obj M ≅ (Scheme.Modules.pullback g).obj N) :
    (pullbackIsoTo f g p h e).hom = pullbackHomTo f g p h e.hom :=
  Category.assoc _ _ _

theorem framedCoefficient_pullbackHomTo
    (eM : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Z) (eN : N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Z)
    (p : X ⟶ Z) (h : f ≫ g = p)
    (q : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N) :
    FramedHom.framedCoefficient (FramedHom.pullbackFrame p eM) (FramedHom.pullbackFrame p eN) (pullbackHomTo f g p h q) =
      f.appTop (FramedHom.framedCoefficient (FramedHom.pullbackFrame g eM) (FramedHom.pullbackFrame g eN) q) := by
  subst p
  have hc := FramedHom.framedCoefficient_pullback (FramedHom.pullbackFrame g eM) (FramedHom.pullbackFrame g eN) f q
  rw [pullbackFrame_comp, pullbackFrame_comp, FramedHom.framedCoefficient_congr] at hc
  exact hc

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback
