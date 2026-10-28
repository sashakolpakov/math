import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramPadded
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutZeroRows
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutEnumeration

namespace OAI.Algorithms

/-! All incidence-indexed rows may be retained. The semantic basis is used only
to count attained signatures, never to select a runtime subset. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutExactBuckets

variable {r Q : ℕ} {I O V : Type*}
variable [Fintype I] [DecidableEq I] [CommRing O]
variable {node : Fin Q → O}

theorem paddedConstraint_spans
    (P : PackingData I (UniversalType r Q 1)) (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q) (g : Fin r) :
    RationalRowSpan
      (LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
        P.completeBlocks t g) (paddedConstraint P A R t g) ∧
    RationalRowSpan (paddedConstraint P A R t g)
      (LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
        P.completeBlocks t g) := by
  classical
  exact ⟨rationalRowSpan_of_row_occurs _ _
      (paddedConstraint_cover P A R denom hdenom units t g),
    rationalRowSpan_of_zero_or_row _ _
      (paddedConstraint_shape P A R denom hdenom units t g)⟩

theorem paddedConstraint_signature
    (P : PackingData I (UniversalType r Q 1)) (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q) (g : Fin r)
    (x y : IncidenceHead P t g → ℤ) :
    signature (paddedConstraint P A R t g) x = signature (paddedConstraint P A R t g) y ↔
    signature (LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
      P.completeBlocks t g) x =
    signature (LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
      P.completeBlocks t g) y := by
  classical
  exact zero_extension_signature_eq_iff _ _
    (paddedConstraint_cover P A R denom hdenom units t g)
    (paddedConstraint_shape P A R denom hdenom units t g) x y

theorem paddedConstraint_rank
    (P : PackingData I (UniversalType r Q 1)) (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q) (g : Fin r) :
    LayoutRank.rowRank (paddedConstraint P A R t g) =
      LayoutRank.rowRank (LayoutBlocks.constraints
        (LayoutUniversal.data A R denom hdenom units) P.completeBlocks t g) := by
  classical
  exact LayoutRank.rowRank_zero_extension _ _
    (paddedConstraint_cover P A R denom hdenom units t g)
    (paddedConstraint_shape P A R denom hdenom units t g)

/-- Fiber-summing preserves both span inclusions. Original variable addresses
are arbitrary labels; no compact renumbering is part of the argument. -/
theorem paddedConstraint_pullback_spans [Fintype V] [DecidableEq V]
    (P : PackingData I (UniversalType r Q 1)) (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q) (g : Fin r)
    (owner : IncidenceHead P t g → V) :
    RationalRowSpan
      (pulledConstraints owner (LayoutBlocks.constraints
        (LayoutUniversal.data A R denom hdenom units) P.completeBlocks t g))
      (pulledConstraints owner (paddedConstraint P A R t g)) ∧
    RationalRowSpan (pulledConstraints owner (paddedConstraint P A R t g))
      (pulledConstraints owner (LayoutBlocks.constraints
        (LayoutUniversal.data A R denom hdenom units) P.completeBlocks t g)) := by
  classical
  obtain ⟨h1,h2⟩ := paddedConstraint_spans P A R denom hdenom units t g
  exact ⟨rationalRowSpan_pullback owner _ _ h1,rationalRowSpan_pullback owner _ _ h2⟩

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
