import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Homology Projection -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.HomologyProjection

noncomputable section

/-! The canonical homology comparison preserves the actual cycle-class
projection. This is the normalization used for coefficient changes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]
  (S : ShortComplex C) [S.HasHomology] (F : C ⥤ D)
  [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]
  [(S.map F).HasHomology]

theorem projection :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let d := S.leftHomologyData
  calc
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
        (S.map F).homologyπ ≫
          ((d.map F).homologyIso.hom ≫ F.map d.homologyIso.inv) :=
      congrArg (fun e => (S.map F).homologyπ ≫ e.hom) (d.mapHomologyIso_eq F)
    _ = ((S.map F).homologyπ ≫ (d.map F).homologyIso.hom) ≫
        F.map d.homologyIso.inv := (Category.assoc _ _ _).symm
    _ = ((d.map F).cyclesIso.hom ≫ F.map d.π) ≫ F.map d.homologyIso.inv :=
      congrArg (fun t => t ≫ F.map d.homologyIso.inv)
        (d.map F).homologyπ_comp_homologyIso_hom
    _ = (d.map F).cyclesIso.hom ≫ F.map (d.π ≫ d.homologyIso.inv) :=
      (Category.assoc _ _ _).trans (congrArg ((d.map F).cyclesIso.hom ≫ ·)
        (F.map_comp _ _).symm)
    _ = (d.map F).cyclesIso.hom ≫ F.map (d.cyclesIso.inv ≫ S.homologyπ) :=
      congrArg (fun t => (d.map F).cyclesIso.hom ≫ F.map t)
        d.π_comp_homologyIso_inv
    _ = ((d.map F).cyclesIso.hom ≫ F.map d.cyclesIso.inv) ≫ F.map S.homologyπ :=
      (congrArg ((d.map F).cyclesIso.hom ≫ ·) (F.map_comp _ _)).trans
        (Category.assoc _ _ _).symm
    _ = (S.mapCyclesIso F).hom ≫ F.map S.homologyπ :=
      congrArg (fun e => e.hom ≫ F.map S.homologyπ) (d.mapCyclesIso_eq F).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.HomologyProjection
