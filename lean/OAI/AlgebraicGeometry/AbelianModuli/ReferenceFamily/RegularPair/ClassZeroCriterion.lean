import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Closed
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.SheafBoundaries

/-! # Class Zero Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassZeroCriterion

noncomputable section

/-! Native degree-one regular sheaf classes vanish exactly when their
actual pair cocycles have regular primitives on the original cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.SheafBoundaries

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens) (v : ∀ i j : I, Γ(X, U i ⊓ U j))

theorem regularPairCechCochain_boundary (s : ∀ i : I, Γ(X, U i)) (hs : Closed.RegularPairPrimitive X U v s) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (X := X.toPresheafedSpace.carrier) (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 0
      (DivisorClass.Chern.Cech.LocalSections.abelianCechLocalSections U (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) (fun i => -s i)) =
      Closed.regularPairCechCochain X U v := by
  funext a
  have hd := DivisorClass.Chern.Cech.LocalSections.abelianCechLocalSections_delta U (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) (fun i => -s i) a
  refine hd.trans ?_
  change X.presheaf.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1)).op (-s (a 1)) -
      X.presheaf.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0)).op (-s (a 0)) =
    X.presheaf.map (homOfLE (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1))).op (v (a 0) (a 1))
  have h := congrArg (fun r => X.presheaf.map
    (homOfLE (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1))).op r) (hs (a 0) (a 1))
  rw [map_sub, Closed.regularSectionRestrict_comp, Closed.regularSectionRestrict_comp] at h
  rw [map_neg, map_neg]
  calc
    _ = X.presheaf.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0)).op (s (a 0)) -
        X.presheaf.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1)).op (s (a 1)) := by abel
    _ = _ := h.symm

theorem regularPairSheafClass_eq_zero_iff_primitive (hU : iSup U = ⊤) (hv : Closed.RegularPairCocycle X U v) :
    Closed.regularPairSheafClass X U hU v hv =
      (0 : (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X.toPresheafedSpace.carrier) 1).obj
        (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf)) ↔
    ∃ s : ∀ i : I, Γ(X, U i), Closed.RegularPairPrimitive X U v s := by
  constructor
  · exact Closed.regularPairPrimitive_of_sheafClass_zero X U v hU hv
  · rintro ⟨s, hs⟩
    exact DivisorClass.Chern.Cech.SheafBoundaries.abelianCechSheafClass_eq_zero_of_boundary U (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hU 0
      (Closed.regularPairCechCochain X U v) (Closed.regularPairCechCochain_closed X U v hv)
      (DivisorClass.Chern.Cech.LocalSections.abelianCechLocalSections U (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) (fun i => -s i))
      (regularPairCechCochain_boundary X U v s hs)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassZeroCriterion
