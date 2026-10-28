import OAI.AlgebraicGeometry.Betti.ProjectivePresentationComparison
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation
import Mathlib.Algebra.DirectSum.Module

/-! # Definitions -/

namespace OAI.Analysis.HodgeTheory.Decomposition.Definitions

noncomputable section

/-! Definitions used in the HodgeDecomposition statement. -/

abbrev Bidegree (n : ℕ) :=
  { pq : ℕ × ℕ // pq.1 + pq.2 = n }

def swapBidegree {n : ℕ} (i : Bidegree n) : Bidegree n :=
  ⟨(i.val.2, i.val.1),
    (Nat.add_comm i.val.2 i.val.1).trans i.property⟩

/-- The existing pure Betti subspace, transported to degree `n`. -/
def hodgePiece (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (n : ℕ) (i : Bidegree n) :
    Submodule ℂ (X.complexCohomology n) :=
  i.property ▸ X.pureBettiSubspace i.val.1 i.val.2

def pureFormsAt (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (n : ℕ) (i : Bidegree n) :
    Submodule ℂ (X.componentForms n) :=
  i.property ▸ X.componentPureForms i.val.1 i.val.2

/-- The filtration on smooth forms, defined independently of cohomology. -/
def filteredForms (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (n : ℕ) (p : ℤ) : Submodule ℂ (X.componentForms n) :=
  ⨆ (i : Bidegree n) (_ : p ≤ (i.val.1 : ℤ)),
    pureFormsAt X n i

/-- Closed filtered forms mapped to Betti cohomology by canonical comparison. -/
def deRhamFiltrationBetti (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (n : ℕ) (p : ℤ) : Submodule ℂ (X.complexCohomology n) :=
  ((filteredForms X n p).comap
    (X.componentClosedForms n).subtype).map
      (X.closedFormBettiClass n)

/-- Pointwise complex conjugation of closed forms on each component. -/
def conjugateClosed (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (n : ℕ) (ω : X.componentClosedForms n) :
    X.componentClosedForms n :=
  (X.componentClosedFormsEquiv n).symm
    (fun C => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm
      (X.componentClosedFormsEquiv n ω C))

end

end OAI.Analysis.HodgeTheory.Decomposition.Definitions
