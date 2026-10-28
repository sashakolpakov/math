import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupClosedSections
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupRefinement
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.AlternatingSum

/-! # Cup Cech Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupCechClass

noncomputable section

/-! The original regular pair cup defines a native sheaf H2 class.
The class and its cocycle witnesses commute with arbitrary cover refinement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

theorem abelianCechDelta_two {X : TopCat} {I : Type} (U : I → Opens X)
    (F : X.Presheaf AddCommGrpCat) (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F U 2) (a : Fin 4 → I) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U 2 k a =
      F.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a (0 : Fin 4).succAbove)).op
        (k (a ∘ (0 : Fin 4).succAbove)) -
      F.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a (1 : Fin 4).succAbove)).op
        (k (a ∘ (1 : Fin 4).succAbove)) +
      F.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a (2 : Fin 4).succAbove)).op
        (k (a ∘ (2 : Fin 4).succAbove)) -
      F.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a (3 : Fin 4).succAbove)).op
        (k (a ∘ (3 : Fin 4).succAbove)) := by
  unfold DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta
  exact Finite.AlternatingSum.finite_alternatingSum_four (fun i =>
    F.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a i.succAbove)).op (k (a ∘ i.succAbove)))

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)

theorem regularPairCupTriple_cech_closed
    (v w : ∀ i j, Γ(X, U i ⊓ U j))
    (hv : RegularPair.Closed.RegularPairCocycle X U v) (hw : RegularPair.Closed.RegularPairCocycle X U w) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 2
      (BoundaryShuffle.regularTripleCechCochain X U (RegularPair.CupSymmetry.regularPairCupTriple X U v w)) = 0 := by
  funext a
  change DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 2
    (BoundaryShuffle.regularTripleCechCochain X U (RegularPair.CupSymmetry.regularPairCupTriple X U v w)) a = 0
  rw [abelianCechDelta_two]
  change (X.presheaf.map _ (X.presheaf.map _ (RegularPair.CupSymmetry.regularPairCupTriple X U v w (a 1) (a 2) (a 3))) :
      Γ(X, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) -
    (X.presheaf.map _ (X.presheaf.map _ (RegularPair.CupSymmetry.regularPairCupTriple X U v w (a 0) (a 2) (a 3))) :
      Γ(X, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) +
    (X.presheaf.map _ (X.presheaf.map _ (RegularPair.CupSymmetry.regularPairCupTriple X U v w (a 0) (a 1) (a 3))) :
      Γ(X, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) -
    (X.presheaf.map _ (X.presheaf.map _ (RegularPair.CupSymmetry.regularPairCupTriple X U v w (a 0) (a 1) (a 2))) :
      Γ(X, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) = 0
  erw [RegularPair.Closed.regularSectionRestrict_comp, RegularPair.Closed.regularSectionRestrict_comp,
    RegularPair.Closed.regularSectionRestrict_comp, RegularPair.Closed.regularSectionRestrict_comp]
  exact CupClosedSections.regularPairCupTriple_quadruple X U v w hv hw (a 0) (a 1) (a 2) (a 3)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 2) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 3)

def regularPairCupSheafClass (hU : iSup U = ⊤)
    (v w : ∀ i j, Γ(X, U i ⊓ U j))
    (hv : RegularPair.Closed.RegularPairCocycle X U v) (hw : RegularPair.Closed.RegularPairCocycle X U w) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X.toPresheafedSpace.carrier) 2).obj
      (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) :=
  DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hU 1
    (BoundaryShuffle.regularTripleCechCochain X U (RegularPair.CupSymmetry.regularPairCupTriple X U v w))
    (regularPairCupTriple_cech_closed X U v w hv hw)

theorem regularPairCupSheafClass_refinement {J : Type} (V : J → X.Opens)
    (r : J → I) (hr : ∀ j, V j ≤ U (r j)) (hU : iSup U = ⊤) (hV : iSup V = ⊤)
    (v w : ∀ i j, Γ(X, U i ⊓ U j))
    (hv : RegularPair.Closed.RegularPairCocycle X U v) (hw : RegularPair.Closed.RegularPairCocycle X U w) :
    regularPairCupSheafClass X V hV
      (RegularPair.Refinement.regularPairRefinement X U V r hr v) (RegularPair.Refinement.regularPairRefinement X U V r hr w)
      (RegularPair.Refinement.regularPairRefinement_cocycle X U V r hr v hv)
      (RegularPair.Refinement.regularPairRefinement_cocycle X U V r hr w hw) =
    regularPairCupSheafClass X U hU v w hv hw := by
  let p := RegularPair.CupSymmetry.regularPairCupTriple X U v w
  have hp := regularPairCupTriple_cech_closed X U v w hv hw
  have H := CupRefinement.regularTripleSheafClass_refinement X U V r hr hU hV p hp
  have he := congrArg (BoundaryShuffle.regularTripleCechCochain X V)
    (CupRefinement.regularPairCupTriple_refinement X U V r hr v w).symm
  exact (Cech.Add.cechSheafClass_congr V (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hV 1
    (BoundaryShuffle.regularTripleCechCochain X V (RegularPair.CupSymmetry.regularPairCupTriple X V
      (RegularPair.Refinement.regularPairRefinement X U V r hr v) (RegularPair.Refinement.regularPairRefinement X U V r hr w)))
    (BoundaryShuffle.regularTripleCechCochain X V (CupRefinement.regularTripleRefinement X U V r hr p))
    (regularPairCupTriple_cech_closed X V _ _
      (RegularPair.Refinement.regularPairRefinement_cocycle X U V r hr v hv)
      (RegularPair.Refinement.regularPairRefinement_cocycle X U V r hr w hw))
    (CupRefinement.regularTripleRefinement_closed X U V r hr p hp) he).trans H

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupCechClass
