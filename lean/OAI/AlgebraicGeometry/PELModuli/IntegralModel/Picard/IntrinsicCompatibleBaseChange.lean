import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.GlobalFunctions
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ModuleHomSheaf
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompatibleBaseChange
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModulePullbackHom
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.NormalizedSquares

/-! # Intrinsic Compatible Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.IntrinsicCompatibleBaseChange.PicardIntrinsicCompatibleBaseChange

noncomputable section

/-! The abstract base-change compatibility acts by the actual native
module pullback square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.GlobalFunctions.PicardFunctions
open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ModuleHomSheaf.PicardModuleHomSheaf

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModulePullbackHom OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.NormalizedSquares.PicardNormalizedSquares

variable {X Y X' Y' : Scheme.{u}} {M N : Y.Modules}

theorem compatible_iff (f : X ⟶ Y)
    (q : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    Isogenies.NeighborCounting.FramedDescent.CompatibleHom f q ↔ Isogenies.NeighborCounting.CompatibleBaseChange.Compatible (F := Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor) f q := by
  constructor
  · intro hq T x y p hx hy
    exact (Isogenies.NeighborCounting.ModulePullbackHom.pullbackHomTo_eq_pullHom x f p hx q).symm.trans
      ((hq x y p hx hy).trans (Isogenies.NeighborCounting.ModulePullbackHom.pullbackHomTo_eq_pullHom y f p hy q))
  · intro hq T x y p hx hy
    exact (Isogenies.NeighborCounting.ModulePullbackHom.pullbackHomTo_eq_pullHom x f p hx q).trans
      ((hq x y p hx hy).trans (Isogenies.NeighborCounting.ModulePullbackHom.pullbackHomTo_eq_pullHom y f p hy q).symm)

theorem baseFrame_apply (g : X' ⟶ Y') (j : Y' ⟶ Y)
    (r : (Scheme.Modules.pullback (g ≫ j)).obj M ⟶ (Scheme.Modules.pullback (g ≫ j)).obj N) :
    (Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor.overMapCompPresheafHomIso M N j).hom.app (op (Over.mk g)) r =
      (Scheme.Modules.pullbackComp g j).hom.app M ≫ r ≫
        (Scheme.Modules.pullbackComp g j).inv.app N := by
  rfl

theorem baseHom_eq (f : X ⟶ Y) (g : X' ⟶ Y') (i : X' ⟶ X) (j : Y' ⟶ Y)
    (h : i ≫ f = g ≫ j)
    (q : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    Isogenies.NeighborCounting.CompatibleBaseChange.baseHom (F := Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor) f g i j h q =
      (NormalizedSquares.PicardNormalizedSquares.sectionSquareIso f j i g h).inv.app M ≫ (Scheme.Modules.pullback i).map q ≫
        (NormalizedSquares.PicardNormalizedSquares.sectionSquareIso f j i g h).hom.app N := by
  let c := Scheme.Modules.pullbackComp g j
  have h₁ : Isogenies.NeighborCounting.CompatibleBaseChange.baseHom (F := Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor) f g i j h q =
      c.hom.app M ≫ pullHom (F := Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor) q i (g ≫ j) (g ≫ j) h h ≫ c.inv.app N :=
    baseFrame_apply g j _
  have h₂ : (c.hom.app M ≫ pullHom (F := Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor) q i (g ≫ j) (g ≫ j) h h ≫ c.inv.app N) =
      c.hom.app M ≫ Isogenies.NeighborCounting.FramedPullback.pullbackHomTo i f (g ≫ j) h q ≫ c.inv.app N :=
    congrArg (fun r ↦ c.hom.app M ≫ r ≫ c.inv.app N)
      (Isogenies.NeighborCounting.ModulePullbackHom.pullbackHomTo_eq_pullHom i f (g ≫ j) h q).symm
  have h₃ : (c.hom.app M ≫ Isogenies.NeighborCounting.FramedPullback.pullbackHomTo i f (g ≫ j) h q ≫ c.inv.app N) =
      (NormalizedSquares.PicardNormalizedSquares.sectionSquareIso f j i g h).inv.app M ≫ (Scheme.Modules.pullback i).map q ≫
        (NormalizedSquares.PicardNormalizedSquares.sectionSquareIso f j i g h).hom.app N := by
    change (c.hom.app M ≫
      ((Scheme.Modules.pullbackComp i f ≪≫ Scheme.Modules.pullbackCongr h).inv.app M ≫
        (Scheme.Modules.pullback i).map q ≫
          (Scheme.Modules.pullbackComp i f ≪≫ Scheme.Modules.pullbackCongr h).hom.app N) ≫
            c.inv.app N) = _
    simp only [NormalizedSquares.PicardNormalizedSquares.sectionSquareIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Category.assoc]
    rfl
  exact h₁.trans (h₂.trans h₃)

theorem baseHom_compatible (f : X ⟶ Y) (g : X' ⟶ Y') (i : X' ⟶ X) (j : Y' ⟶ Y)
    (h : i ≫ f = g ≫ j)
    (q : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (hq : Isogenies.NeighborCounting.FramedDescent.CompatibleHom f q) :
    Isogenies.NeighborCounting.FramedDescent.CompatibleHom g ((NormalizedSquares.PicardNormalizedSquares.sectionSquareIso f j i g h).inv.app M ≫
      (Scheme.Modules.pullback i).map q ≫ (NormalizedSquares.PicardNormalizedSquares.sectionSquareIso f j i g h).hom.app N) := by
  have ha : Isogenies.NeighborCounting.CompatibleBaseChange.Compatible (F := Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor) g
      (Isogenies.NeighborCounting.CompatibleBaseChange.baseHom (F := Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor) f g i j h q) :=
    Isogenies.NeighborCounting.CompatibleBaseChange.baseHom_compatible (F := Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor)
      (M := M) (N := N) f g i j h q ((compatible_iff f q).mp hq)
  have hb : Isogenies.NeighborCounting.FramedDescent.CompatibleHom g (Isogenies.NeighborCounting.CompatibleBaseChange.baseHom
      (F := Isogenies.NeighborCounting.ModulePullbackHom.modulePullbackFunctor) f g i j h q) :=
    (compatible_iff g _).mpr ha
  intro T x y p hx hy
  have he := baseHom_eq f g i j h q
  exact (congrArg (Isogenies.NeighborCounting.FramedPullback.pullbackHomTo x g p hx) he).symm.trans
    ((hb x y p hx hy).trans (congrArg (Isogenies.NeighborCounting.FramedPullback.pullbackHomTo y g p hy) he))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.IntrinsicCompatibleBaseChange.PicardIntrinsicCompatibleBaseChange
