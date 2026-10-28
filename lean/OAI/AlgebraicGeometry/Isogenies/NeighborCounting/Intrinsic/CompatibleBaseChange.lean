import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompatibleBaseChange
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModulePullbackHom
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.NormalizedSquares

/-! # Compatible Base Change -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CompatibleBaseChange

noncomputable section

/-! The abstract base-change compatibility acts by the actual native
module pullback square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModulePullbackHom OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent OAI.AlgebraicGeometry.Isogenies.NeighborCounting.NormalizedSquares

variable {X Y X' Y' : Scheme.{u}} {M N : Y.Modules}

theorem compatible_iff (f : X ⟶ Y)
    (q : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    FramedDescent.CompatibleHom f q ↔ CompatibleBaseChange.Compatible (F := ModulePullbackHom.modulePullbackFunctor) f q := by
  constructor
  · intro hq T x y p hx hy
    exact (ModulePullbackHom.pullbackHomTo_eq_pullHom x f p hx q).symm.trans
      ((hq x y p hx hy).trans (ModulePullbackHom.pullbackHomTo_eq_pullHom y f p hy q))
  · intro hq T x y p hx hy
    exact (ModulePullbackHom.pullbackHomTo_eq_pullHom x f p hx q).trans
      ((hq x y p hx hy).trans (ModulePullbackHom.pullbackHomTo_eq_pullHom y f p hy q).symm)

theorem baseFrame_apply (g : X' ⟶ Y') (j : Y' ⟶ Y)
    (r : (Scheme.Modules.pullback (g ≫ j)).obj M ⟶ (Scheme.Modules.pullback (g ≫ j)).obj N) :
    (ModulePullbackHom.modulePullbackFunctor.overMapCompPresheafHomIso M N j).hom.app (op (Over.mk g)) r =
      (Scheme.Modules.pullbackComp g j).hom.app M ≫ r ≫
        (Scheme.Modules.pullbackComp g j).inv.app N := by
  rfl

theorem baseHom_eq (f : X ⟶ Y) (g : X' ⟶ Y') (i : X' ⟶ X) (j : Y' ⟶ Y)
    (h : i ≫ f = g ≫ j)
    (q : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    CompatibleBaseChange.baseHom (F := ModulePullbackHom.modulePullbackFunctor) f g i j h q =
      (NormalizedSquares.sectionSquareIso f j i g h).inv.app M ≫ (Scheme.Modules.pullback i).map q ≫
        (NormalizedSquares.sectionSquareIso f j i g h).hom.app N := by
  let c := Scheme.Modules.pullbackComp g j
  have h₁ : CompatibleBaseChange.baseHom (F := ModulePullbackHom.modulePullbackFunctor) f g i j h q =
      c.hom.app M ≫ pullHom (F := ModulePullbackHom.modulePullbackFunctor) q i (g ≫ j) (g ≫ j) h h ≫ c.inv.app N :=
    baseFrame_apply g j _
  have h₂ : (c.hom.app M ≫ pullHom (F := ModulePullbackHom.modulePullbackFunctor) q i (g ≫ j) (g ≫ j) h h ≫ c.inv.app N) =
      c.hom.app M ≫ FramedPullback.pullbackHomTo i f (g ≫ j) h q ≫ c.inv.app N :=
    congrArg (fun r ↦ c.hom.app M ≫ r ≫ c.inv.app N)
      (ModulePullbackHom.pullbackHomTo_eq_pullHom i f (g ≫ j) h q).symm
  have h₃ : (c.hom.app M ≫ FramedPullback.pullbackHomTo i f (g ≫ j) h q ≫ c.inv.app N) =
      (NormalizedSquares.sectionSquareIso f j i g h).inv.app M ≫ (Scheme.Modules.pullback i).map q ≫
        (NormalizedSquares.sectionSquareIso f j i g h).hom.app N := by
    change (c.hom.app M ≫
      ((Scheme.Modules.pullbackComp i f ≪≫ Scheme.Modules.pullbackCongr h).inv.app M ≫
        (Scheme.Modules.pullback i).map q ≫
          (Scheme.Modules.pullbackComp i f ≪≫ Scheme.Modules.pullbackCongr h).hom.app N) ≫
            c.inv.app N) = _
    simp only [NormalizedSquares.sectionSquareIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Category.assoc]
    rfl
  exact h₁.trans (h₂.trans h₃)

theorem baseHom_compatible (f : X ⟶ Y) (g : X' ⟶ Y') (i : X' ⟶ X) (j : Y' ⟶ Y)
    (h : i ≫ f = g ≫ j)
    (q : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (hq : FramedDescent.CompatibleHom f q) :
    FramedDescent.CompatibleHom g ((NormalizedSquares.sectionSquareIso f j i g h).inv.app M ≫
      (Scheme.Modules.pullback i).map q ≫ (NormalizedSquares.sectionSquareIso f j i g h).hom.app N) := by
  have ha : CompatibleBaseChange.Compatible (F := ModulePullbackHom.modulePullbackFunctor) g
      (CompatibleBaseChange.baseHom (F := ModulePullbackHom.modulePullbackFunctor) f g i j h q) :=
    NeighborCounting.CompatibleBaseChange.baseHom_compatible (F := ModulePullbackHom.modulePullbackFunctor)
      (M := M) (N := N) f g i j h q ((compatible_iff f q).mp hq)
  have hb : FramedDescent.CompatibleHom g (CompatibleBaseChange.baseHom
      (F := ModulePullbackHom.modulePullbackFunctor) f g i j h q) :=
    (compatible_iff g _).mpr ha
  intro T x y p hx hy
  have he := baseHom_eq f g i j h q
  exact (congrArg (FramedPullback.pullbackHomTo x g p hx) he).symm.trans
    ((hb x y p hx hy).trans (congrArg (FramedPullback.pullbackHomTo y g p hy) he))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CompatibleBaseChange
