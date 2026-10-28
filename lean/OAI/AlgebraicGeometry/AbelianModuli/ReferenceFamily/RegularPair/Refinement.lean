import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Closed
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.Add
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.ClassRefinement

/-! # Refinement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Refinement

noncomputable section

/-! Refining a cover restricts the original regular pair sections.
These literal restrictions retain both the cocycle equation and the
original native degree-one sheaf class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.ClassRefinement

variable (X : Scheme.{0}) {I J : Type} (U : I → X.Opens) (V : J → X.Opens)
    (r : J → I) (hr : ∀ j, V j ≤ U (r j)) (v : ∀ i j : I, Γ(X, U i ⊓ U j))

def regularPairRefinement (i j : J) : Γ(X, V i ⊓ V j) :=
  X.presheaf.map (homOfLE (inf_le_inf (hr i) (hr j))).op (v (r i) (r j))

theorem regularPairRefinement_cocycle (hv : Closed.RegularPairCocycle X U v) :
    Closed.RegularPairCocycle X V (regularPairRefinement X U V r hr v) := by
  intro i j l
  have H := congrArg (fun s => X.presheaf.map
    (homOfLE (inf_le_inf (inf_le_inf (hr i) (hr j)) (hr l))).op s) (hv (r i) (r j) (r l))
  rw [map_add, Closed.regularSectionRestrict_comp, Closed.regularSectionRestrict_comp, Closed.regularSectionRestrict_comp] at H
  dsimp only [regularPairRefinement]
  rw [Closed.regularSectionRestrict_comp, Closed.regularSectionRestrict_comp, Closed.regularSectionRestrict_comp]
  exact H

theorem regularPairRefinement_cech :
    Closed.regularPairCechCochain X V (regularPairRefinement X U V r hr v) =
      DivisorClass.Chern.Cech.AbelianRefinement.abelianCechRefinementMap U V r hr (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj 1 (Closed.regularPairCechCochain X U v) := by
  funext a
  change X.presheaf.map _ (X.presheaf.map _ (v (r (a 0)) (r (a 1)))) =
    X.presheaf.map _ (X.presheaf.map _ (v (r (a 0)) (r (a 1))))
  rw [Closed.regularSectionRestrict_comp, Closed.regularSectionRestrict_comp]

theorem regularPairSheafClass_refinement (hU : iSup U = ⊤) (hV : iSup V = ⊤)
    (hv : Closed.RegularPairCocycle X U v) :
    Closed.regularPairSheafClass X V hV (regularPairRefinement X U V r hr v) (regularPairRefinement_cocycle X U V r hr v hv) =
      Closed.regularPairSheafClass X U hU v hv := by
  have H := DivisorClass.Chern.Cech.ClassRefinement.abelianCechSheafClass_refinement U V r hr (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hU hV 0
    (Closed.regularPairCechCochain X U v) (Closed.regularPairCechCochain_closed X U v hv)
  have hc := regularPairRefinement_cech X U V r hr v
  exact (Cech.Add.cechSheafClass_congr V (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hV 0
    (Closed.regularPairCechCochain X V (regularPairRefinement X U V r hr v))
    (DivisorClass.Chern.Cech.AbelianRefinement.abelianCechRefinementMap U V r hr (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj 1 (Closed.regularPairCechCochain X U v))
    (Closed.regularPairCechCochain_closed X V _ (regularPairRefinement_cocycle X U V r hr v hv))
    (DivisorClass.Chern.Cech.ClassRefinement.abelianCechRefinementMap_closed U V r hr (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj 1 _
      (Closed.regularPairCechCochain_closed X U v hv)) hc).trans H

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Refinement
