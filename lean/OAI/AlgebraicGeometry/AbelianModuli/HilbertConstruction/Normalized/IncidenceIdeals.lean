import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ConditionIdeals
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.IncidenceScheme

/-! # Incidence Ideals -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.IncidenceIdeals

noncomputable section

/-!
The defining ideal of the normalized incidence locus, characterized by its
vanishing after pullback to every scheme-valued parameter point.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ : Type u} [Fintype ι] [Fintype ν] [Fintype μ]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq μ]
variable {S : Scheme.{u}} (M : Over S) (a : ι → ν)
variable (Q : Matrix ι ν Γ(M.left, ⊤)) (hQ : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a Q)
variable (K : Matrix κ μ Γ(M.left, ⊤)) (F : Matrix μ ν Γ(M.left, ⊤))

def normalizedIncidenceClosedModel :
    Closed.ConditionIdeals.ClosedConditionModel (IncidenceScheme.normalizedIncidenceSubfunctor M a Q hQ K F) := by
  apply Classical.choice
  let s (p : κ × ν) : Γ(M.left, ⊤) := Incidence.normalizedIncidenceMatrix a Q K F p.1 p.2
  obtain ⟨Z, j, hj, hZ⟩ := HilbertScheme.Presentations.EquationLoci.finite_equations_closed_locus [HilbertScheme.Presentations.SectionZeroLocus.sectionEquation M s]
  refine ⟨⟨Z, j, hj, ?_⟩⟩
  intro T f
  change IncidenceScheme.normalizedIncidenceCondition Q K F f.left.appTop.hom ↔ _
  exact (IncidenceScheme.normalizedIncidenceCondition_iff a Q hQ K F f.left.appTop.hom).trans
    ((HilbertScheme.Presentations.SectionZeroLocus.sectionEquation_satisfies M s f).symm.trans (hZ T f))

def normalizedIncidenceIdeal : M.left.IdealSheafData :=
  (normalizedIncidenceClosedModel M a Q hQ K F).ideal

theorem normalizedIncidenceIdeal_vanish_iff {T : Over S} (f : T ⟶ M) :
    (normalizedIncidenceIdeal M a Q hQ K F).comap f.left = ⊥ ↔
      IncidenceScheme.normalizedIncidenceCondition Q K F f.left.appTop.hom :=
  (normalizedIncidenceClosedModel M a Q hQ K F).ideal_vanish_iff f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.IncidenceIdeals
