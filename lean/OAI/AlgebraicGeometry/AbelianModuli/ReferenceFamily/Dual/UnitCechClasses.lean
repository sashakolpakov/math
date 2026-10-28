import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCechCoefficients
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.CategoryTheory.Sites.Whiskering

/-! # Unit Cech Classes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCechClasses

noncomputable section

/-! The cohomology class of actual normalized dual-number transition
units is unchanged by actual normalized changes of local frame. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}}

def ringAdditiveSheaf (R : TopCat.Sheaf CommRingCat.{0} X) : TopCat.Sheaf AddCommGrpCat.{0} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ RingCat AddCommGrpCat)).obj
    ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat)).obj R)

variable (R : TopCat.Sheaf CommRingCat.{0} X) {I : Type} (U : I → Opens X)

def dualUnitCechClass (hU : iSup U = ⊤) (u : UnitCechCoefficients.DualUnitCechCoefficients R.obj U)
    (hu : UnitCechCoefficients.DualUnitCechNormalized R.obj U u) (hc : UnitCechCoefficients.DualUnitCechCocycle R.obj U u) :
    CategoryTheory.Sheaf.H (ringAdditiveSheaf R) 1 :=
  DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U (ringAdditiveSheaf R) hU 0 (UnitCechCoefficients.dualUnitCechAdditive R.obj U u)
    (UnitCechCoefficients.dualUnitCechAdditive_closed R.obj U u hu hc)

theorem dualUnitCech_gauge_boundary (u v : UnitCechCoefficients.DualUnitCechCoefficients R.obj U)
    (hu : UnitCechCoefficients.DualUnitCechNormalized R.obj U u)
    (g : ∀ i, (DualNumber (R.obj.obj (op (U i))))ˣ) (hg : ∀ i, (g i).val.fst = 1)
    (hv : ∀ a : Fin 2 → I, v a = u a *
      UnitCechCoefficients.dualCechRestrict R.obj (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1) (g (a 1)) /
      UnitCechCoefficients.dualCechRestrict R.obj (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (g (a 0))) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (ringAdditiveSheaf R).obj U 0
      (DivisorClass.Chern.Cech.LocalSections.abelianCechLocalSections U (ringAdditiveSheaf R) (fun i => (g i).val.snd)) =
        UnitCechCoefficients.dualUnitCechAdditive R.obj U v - UnitCechCoefficients.dualUnitCechAdditive R.obj U u := by
  funext a
  erw [DivisorClass.Chern.Cech.LocalSections.abelianCechLocalSections_delta]
  have h := congrArg (fun w : (DualNumber (R.obj.obj (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))))ˣ => w.val.snd) (hv a)
  rw [UnitCoordinates.dualUnit_snd_gauge _ _ _ (hu a)
    (UnitCechCoefficients.dualCechRestrict_fst R.obj _ _ (hg _)) (UnitCechCoefficients.dualCechRestrict_fst R.obj _ _ (hg _))] at h
  change R.obj.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1)).op (g (a 1)).val.snd -
      R.obj.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0)).op (g (a 0)).val.snd =
        (v a).val.snd - (u a).val.snd
  rw [h, UnitCechCoefficients.dualCechRestrict_snd, UnitCechCoefficients.dualCechRestrict_snd]
  abel

theorem dualUnitCechClass_gauge (hU : iSup U = ⊤) (u v : UnitCechCoefficients.DualUnitCechCoefficients R.obj U)
    (hu : UnitCechCoefficients.DualUnitCechNormalized R.obj U u) (hv : UnitCechCoefficients.DualUnitCechNormalized R.obj U v)
    (hcu : UnitCechCoefficients.DualUnitCechCocycle R.obj U u) (hcv : UnitCechCoefficients.DualUnitCechCocycle R.obj U v)
    (g : ∀ i, (DualNumber (R.obj.obj (op (U i))))ˣ) (hg : ∀ i, (g i).val.fst = 1)
    (he : ∀ a : Fin 2 → I, v a = u a *
      UnitCechCoefficients.dualCechRestrict R.obj (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1) (g (a 1)) /
      UnitCechCoefficients.dualCechRestrict R.obj (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (g (a 0))) :
    dualUnitCechClass R U hU v hv hcv = dualUnitCechClass R U hU u hu hcu := by
  let F := ringAdditiveSheaf R
  let : AddCommGroup (CategoryTheory.Sheaf.H F 1) := Cech.Add.cechClassAddCommGroup F 1
  have hku := UnitCechCoefficients.dualUnitCechAdditive_closed R.obj U u hu hcu
  have hkv := UnitCechCoefficients.dualUnitCechAdditive_closed R.obj U v hv hcv
  have hz := DivisorClass.Chern.Cech.SheafBoundaries.abelianCechSheafClass_eq_zero_of_boundary U F hU 0
    (UnitCechCoefficients.dualUnitCechAdditive R.obj U v - UnitCechCoefficients.dualUnitCechAdditive R.obj U u)
    (Cech.Add.cechSub_closed U F.obj 1 _ _ hkv hku)
    (DivisorClass.Chern.Cech.LocalSections.abelianCechLocalSections U F (fun i => (g i).val.snd))
    (dualUnitCech_gauge_boundary R U u v hu g hg he)
  exact sub_eq_zero.mp ((Cech.Add.cechSheafClass_sub U F hU 0 _ _ hkv hku).symm.trans hz)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCechClasses
