import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.TransitionCocycle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.LineSections

/-! # Cech Generator -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CechGenerator

noncomputable section

section

/-! Pairwise regular transitions give coefficients on the original
Cech intersections, with their literal restriction formulas. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X : Scheme.{0}} {I : Type} (U : I → X.Opens)

theorem cechIntersection_le_component (n : ℕ) (a : Fin (n + 1) → I) (k : Fin (n + 1)) :
    Cech.ExtensionCoordinates.cechIntersection U n a ≤ U (a k) :=
  leOfHom (Pi.π (fun j : Fin (n + 1) => U (a j)) k)

theorem cechFaceIndex_zero_eval (a : Fin 2 → I) : Cech.ExtensionCoordinates.cechFaceIndex 0 0 a 0 = a 1 := rfl
theorem cechFaceIndex_one_eval (a : Fin 2 → I) : Cech.ExtensionCoordinates.cechFaceIndex 0 1 a 0 = a 0 := rfl

def regularCechTransition (r : TransitionCocycle.RegularTransitionCoefficients U) (a : Fin 2 → I) :
    Γ(X, Cech.ExtensionCoordinates.cechIntersection U 1 a)ˣ :=
  TransitionCocycle.regularTransitionOn U r (a 0) (a 1) (Cech.ExtensionCoordinates.cechIntersection U 1 a)
    (cechIntersection_le_component U 1 a 0) (cechIntersection_le_component U 1 a 1)

def regularCechCoefficients (r : TransitionCocycle.RegularTransitionCoefficients U) (a : Fin 2 → I) :
    Γ(X, Cech.ExtensionCoordinates.cechIntersection U 1 a) := (regularCechTransition U r a).val

theorem regularTransitionOn_restrict_val (r : TransitionCocycle.RegularTransitionCoefficients U) (i j : I)
    {V W : X.Opens} (h : W ≤ V) (hi : V ≤ U i) (hj : V ≤ U j) :
    X.presheaf.map (homOfLE h).op (TransitionCocycle.regularTransitionOn U r i j V hi hj).val =
      (TransitionCocycle.regularTransitionOn U r i j W (h.trans hi) (h.trans hj)).val :=
  congrArg Units.val (TransitionCocycle.regularTransitionOn_restrict U r i j h hi hj)

theorem regularCechCoefficients_restrict (r : TransitionCocycle.RegularTransitionCoefficients U) (a : Fin 2 → I)
    {W : X.Opens} (h : W ≤ Cech.ExtensionCoordinates.cechIntersection U 1 a) :
    X.presheaf.map (homOfLE h).op (regularCechCoefficients U r a) =
      (TransitionCocycle.regularTransitionOn U r (a 0) (a 1) W
        (h.trans (cechIntersection_le_component U 1 a 0))
        (h.trans (cechIntersection_le_component U 1 a 1))).val :=
  regularTransitionOn_restrict_val U r (a 0) (a 1) h _ _

end

/-! A regular transition cocycle supplies an actual local generator
of its kernel sheaf, with its original coordinates and restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.TopCat.Sheaf

variable {X : Scheme.{0}} {I : Type} (U : I → X.Opens)
    (r : TransitionCocycle.RegularTransitionCoefficients U)

def regularCechGenerator (j : I) (W : X.Opens) (hW : W ≤ U j) : Γ(Cech.TermModules.cechTermModule X U 0, W) :=
  (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv (Cech.TermModules.structureAbelianSheaf X) U 0 W).symm
    (fun a => (TransitionCocycle.regularTransitionOn U r j (a 0) (W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 a)
      (inf_le_left.trans hW) (inf_le_right.trans (cechIntersection_le_component U 0 a 0))).val)

theorem regularCechGenerator_coefficient (j : I) (W : X.Opens) (hW : W ≤ U j) (a : Fin 1 → I) :
    Cech.ExtensionCoordinates.cechCoefficient U 0 W (regularCechGenerator U r j W hW) a =
      (TransitionCocycle.regularTransitionOn U r j (a 0) (W ⊓ Cech.ExtensionCoordinates.cechIntersection U 0 a)
        (inf_le_left.trans hW) (inf_le_right.trans (cechIntersection_le_component U 0 a 0))).val :=
  congrArg (fun b => b a)
    ((SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv (Cech.TermModules.structureAbelianSheaf X) U 0 W).apply_symm_apply _)

theorem regularCechGenerator_restrict (j : I) {V W : X.Opens} (h : W ≤ V) (hV : V ≤ U j) :
    (Cech.TermModules.cechTermModule X U 0).presheaf.map (homOfLE h).op (regularCechGenerator U r j V hV) =
      regularCechGenerator U r j W (h.trans hV) := by
  apply (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv (Cech.TermModules.structureAbelianSheaf X) U 0 W).injective
  funext a
  change Cech.ExtensionCoordinates.cechCoefficient U 0 W _ a = Cech.ExtensionCoordinates.cechCoefficient U 0 W _ a
  rw [Cech.ExtensionCoordinates.cechCoefficient_restrict, regularCechGenerator_coefficient, regularCechGenerator_coefficient,
    regularTransitionOn_restrict_val]

theorem regularCechGenerator_compatible (hr : TransitionCocycle.RegularTransitionCocycle U r)
    (j : I) (W : X.Opens) (hW : W ≤ U j) :
    Cech.LineSections.CechLineCompatible U (regularCechCoefficients U r) W (regularCechGenerator U r j W hW) := by
  intro a
  rw [regularCechGenerator_coefficient, regularCechGenerator_coefficient,
    regularTransitionOn_restrict_val, regularTransitionOn_restrict_val, regularCechCoefficients_restrict]
  have h := TransitionCocycle.regularTransition_cocycle_on U r hr j (a 0) (a 1) (W ⊓ Cech.ExtensionCoordinates.cechIntersection U 1 a)
    (inf_le_left.trans hW) (inf_le_right.trans (cechIntersection_le_component U 1 a 0))
    (inf_le_right.trans (cechIntersection_le_component U 1 a 1))
  exact congrArg Units.val (h.symm.trans (mul_comm _ _))

def regularCechLineGenerator (hr : TransitionCocycle.RegularTransitionCocycle U r) (j : I) :
    Γ(Cech.LineModule.cechLineModule U (regularCechCoefficients U r), U j) :=
  Cech.LineSections.cechLineSectionLift U (regularCechCoefficients U r) (U j) (regularCechGenerator U r j (U j) le_rfl)
    (regularCechGenerator_compatible U r hr j (U j) le_rfl)

theorem regularCechLineGenerator_inclusion (hr : TransitionCocycle.RegularTransitionCocycle U r) (j : I) :
    (Cech.LineModule.cechLineModuleInclusion U (regularCechCoefficients U r)).app (U j) (regularCechLineGenerator U r hr j) =
      regularCechGenerator U r j (U j) le_rfl :=
  Cech.LineSections.cechLineSectionLift_inclusion U (regularCechCoefficients U r) (U j) _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CechGenerator
