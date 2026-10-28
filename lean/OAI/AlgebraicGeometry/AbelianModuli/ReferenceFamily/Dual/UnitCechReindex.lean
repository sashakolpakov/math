import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCechClasses
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.ClassRefinement

/-! # Unit Cech Reindex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCechReindex

noncomputable section

/-! Reindexing an actual normalized dual-number cocycle preserves
its original sheaf cohomology class whenever the selected opens cover. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.ClassRefinement

variable {X : TopCat.{0}} (R : TopCat.Sheaf CommRingCat.{0} X)
    {I J : Type} (U : I → Opens X) (r : J → I)

def dualUnitCechReindex (u : UnitCechCoefficients.DualUnitCechCoefficients R.obj U) :
    UnitCechCoefficients.DualUnitCechCoefficients R.obj (U ∘ r) := fun a => u (r ∘ a)

theorem dualUnitCechReindex_normalized (u : UnitCechCoefficients.DualUnitCechCoefficients R.obj U)
    (hu : UnitCechCoefficients.DualUnitCechNormalized R.obj U u) :
    UnitCechCoefficients.DualUnitCechNormalized R.obj (U ∘ r) (dualUnitCechReindex R U r u) := fun a => hu (r ∘ a)

theorem dualUnitCechReindex_cocycle (u : UnitCechCoefficients.DualUnitCechCoefficients R.obj U)
    (hc : UnitCechCoefficients.DualUnitCechCocycle R.obj U u) :
    UnitCechCoefficients.DualUnitCechCocycle R.obj (U ∘ r) (dualUnitCechReindex R U r u) := fun a => hc (r ∘ a)

theorem dualUnitCechReindex_additive (u : UnitCechCoefficients.DualUnitCechCoefficients R.obj U) :
    DivisorClass.Chern.Cech.AbelianRefinement.abelianCechRefinementMap U (U ∘ r) r (fun _ => le_rfl) (UnitCechClasses.ringAdditiveSheaf R).obj 1
      (UnitCechCoefficients.dualUnitCechAdditive R.obj U u) =
        UnitCechCoefficients.dualUnitCechAdditive R.obj (U ∘ r) (dualUnitCechReindex R U r u) := by
  funext a
  change R.obj.map (𝟙 (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (r ∘ a)))) (u (r ∘ a)).val.snd = (u (r ∘ a)).val.snd
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem dualUnitCechClass_reindex (hU : iSup U = ⊤) (hV : iSup (U ∘ r) = ⊤)
    (u : UnitCechCoefficients.DualUnitCechCoefficients R.obj U) (hu : UnitCechCoefficients.DualUnitCechNormalized R.obj U u)
    (hc : UnitCechCoefficients.DualUnitCechCocycle R.obj U u) :
    UnitCechClasses.dualUnitCechClass R (U ∘ r) hV (dualUnitCechReindex R U r u)
      (dualUnitCechReindex_normalized R U r u hu) (dualUnitCechReindex_cocycle R U r u hc) =
        UnitCechClasses.dualUnitCechClass R U hU u hu hc := by
  have h := DivisorClass.Chern.Cech.ClassRefinement.abelianCechSheafClass_refinement U (U ∘ r) r (fun _ => le_rfl)
    (UnitCechClasses.ringAdditiveSheaf R) hU hV 0 (UnitCechCoefficients.dualUnitCechAdditive R.obj U u)
    (UnitCechCoefficients.dualUnitCechAdditive_closed R.obj U u hu hc)
  exact (Cech.Add.cechSheafClass_congr (U ∘ r) (UnitCechClasses.ringAdditiveSheaf R) hV 0 _ _ _ _
    (dualUnitCechReindex_additive R U r u).symm).trans h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCechReindex
