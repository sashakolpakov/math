import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Refinement
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.CupSymmetry

/-! # Cup Refinement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupRefinement

noncomputable section

/-! Refinement preserves the original regular cup sections and their
literal boundary witnesses, on arbitrary algebraic covers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Scheme.{0}) {I J : Type} (U : I → X.Opens) (V : J → X.Opens)
    (r : J → I) (hr : ∀ j, V j ≤ U (r j))

def regularTripleRefinement (w : ∀ i j l : I, Γ(X, (U i ⊓ U j) ⊓ U l))
    (i j l : J) : Γ(X, (V i ⊓ V j) ⊓ V l) :=
  X.presheaf.map (homOfLE (inf_le_inf (inf_le_inf (hr i) (hr j)) (hr l))).op
    (w (r i) (r j) (r l))

theorem regularPairCupTriple_refinement (v w : ∀ i j : I, Γ(X, U i ⊓ U j)) :
    regularTripleRefinement X U V r hr (RegularPair.CupSymmetry.regularPairCupTriple X U v w) =
      RegularPair.CupSymmetry.regularPairCupTriple X V (RegularPair.Refinement.regularPairRefinement X U V r hr v)
        (RegularPair.Refinement.regularPairRefinement X U V r hr w) := by
  funext i j l
  dsimp only [regularTripleRefinement, RegularPair.CupSymmetry.regularPairCupTriple, RegularPair.Refinement.regularPairRefinement]
  rw [map_mul, RegularPair.Closed.regularSectionRestrict_comp, RegularPair.Closed.regularSectionRestrict_comp,
    RegularPair.Closed.regularSectionRestrict_comp, RegularPair.Closed.regularSectionRestrict_comp]

theorem regularTripleRefinement_boundary
    (v : ∀ i j : I, Γ(X, U i ⊓ U j))
    (w : ∀ i j l : I, Γ(X, (U i ⊓ U j) ⊓ U l)) (hw : BoundaryShuffle.RegularTripleBoundary X U v w) :
    BoundaryShuffle.RegularTripleBoundary X V (RegularPair.Refinement.regularPairRefinement X U V r hr v)
      (regularTripleRefinement X U V r hr w) := by
  intro i j l
  have H := congrArg (fun s => X.presheaf.map
    (homOfLE (inf_le_inf (inf_le_inf (hr i) (hr j)) (hr l))).op s)
      (hw (r i) (r j) (r l))
  rw [map_add, map_sub, RegularPair.Closed.regularSectionRestrict_comp, RegularPair.Closed.regularSectionRestrict_comp,
    RegularPair.Closed.regularSectionRestrict_comp] at H
  dsimp only [RegularPair.Refinement.regularPairRefinement, regularTripleRefinement]
  rw [RegularPair.Closed.regularSectionRestrict_comp, RegularPair.Closed.regularSectionRestrict_comp, RegularPair.Closed.regularSectionRestrict_comp]
  exact H

theorem regularTripleRefinement_cech
    (w : ∀ i j l : I, Γ(X, (U i ⊓ U j) ⊓ U l)) :
    BoundaryShuffle.regularTripleCechCochain X V (regularTripleRefinement X U V r hr w) =
      DivisorClass.Chern.Cech.AbelianRefinement.abelianCechRefinementMap U V r hr (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj 2
        (BoundaryShuffle.regularTripleCechCochain X U w) := by
  funext a
  change X.presheaf.map _ (X.presheaf.map _ (w (r (a 0)) (r (a 1)) (r (a 2)))) =
    X.presheaf.map _ (X.presheaf.map _ (w (r (a 0)) (r (a 1)) (r (a 2))))
  rw [RegularPair.Closed.regularSectionRestrict_comp, RegularPair.Closed.regularSectionRestrict_comp]

theorem regularTripleRefinement_closed
    (w : ∀ i j l : I, Γ(X, (U i ⊓ U j) ⊓ U l))
    (hw : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 2
      (BoundaryShuffle.regularTripleCechCochain X U w) = 0) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj V 2
      (BoundaryShuffle.regularTripleCechCochain X V (regularTripleRefinement X U V r hr w)) = 0 := by
  rw [regularTripleRefinement_cech]
  exact DivisorClass.Chern.Cech.ClassRefinement.abelianCechRefinementMap_closed U V r hr (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj 2 _ hw

theorem regularTripleSheafClass_refinement (hU : iSup U = ⊤) (hV : iSup V = ⊤)
    (w : ∀ i j l : I, Γ(X, (U i ⊓ U j) ⊓ U l))
    (hw : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 2
      (BoundaryShuffle.regularTripleCechCochain X U w) = 0) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass V (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hV 1
      (BoundaryShuffle.regularTripleCechCochain X V (regularTripleRefinement X U V r hr w))
      (regularTripleRefinement_closed X U V r hr w hw) =
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hU 1
      (BoundaryShuffle.regularTripleCechCochain X U w) hw := by
  have H := DivisorClass.Chern.Cech.ClassRefinement.abelianCechSheafClass_refinement U V r hr (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hU hV 1
    (BoundaryShuffle.regularTripleCechCochain X U w) hw
  exact (Cech.Add.cechSheafClass_congr V (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hV 1
    (BoundaryShuffle.regularTripleCechCochain X V (regularTripleRefinement X U V r hr w))
    (DivisorClass.Chern.Cech.AbelianRefinement.abelianCechRefinementMap U V r hr (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj 2
      (BoundaryShuffle.regularTripleCechCochain X U w))
    (regularTripleRefinement_closed X U V r hr w hw)
    (DivisorClass.Chern.Cech.ClassRefinement.abelianCechRefinementMap_closed U V r hr (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj 2 _ hw)
    (regularTripleRefinement_cech X U V r hr w)).trans H

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupRefinement
