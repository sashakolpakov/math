import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointCompact
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointActiveData
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CompactSubgroupBaseChange

/-! # Point Compact Kernel Frobenius -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! The supplied compact subgroup representatives have actual embedded
Frobenius pullback isomorphisms, derived from their literal all-test
whole/identity condition and the original ordinary point data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable (D : Integral.Construction.SplitPELReduction P iota κ M U B q)
variable {K' : Type} [Field K'] [NumberField K'] {κ' : K' →+* ℂ}
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K' κ' q) (iota' : E →+* K') (hsplit : j.HasSplitCoordinates iota')
variable (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
variable (O : D.OrdinaryKernelData j iota' hsplit labels)
variable (C0 : D.CompactKernelPrescription j iota' hsplit labels)
variable (hC0 : D.CompactKernelCondition j iota' hsplit labels O C0)

include hC0 in
theorem Integral.Construction.SplitPELReduction.exists_compactKernelFrobeniusIso (x : D.OrdinaryPoint) (n : ℕ) (v : Fin s) :
    ∃ e : (Over.pullback D.nativeIntegralGeometricFrobenius.left).obj (C0 x n v).group.X ≅
        (C0 (D.ordinaryFrobenius x) n v).group.X,
      e.hom ≫ (C0 (D.ordinaryFrobenius x) n v).inclusion.hom.hom =
        (Over.pullback D.nativeIntegralGeometricFrobenius.left).map (C0 x n v).inclusion.hom.hom ≫
          (D.pointFrobeniusBlockIso j iota' hsplit x n (labels (v.succ, false))).hom.hom.hom := by
  let xF := D.ordinaryFrobenius x
  have : IsClosedImmersion (C0 x n v).inclusion.hom.hom.left := (C0 x n v).closed
  have hSource : Mono (C0 x n v).inclusion.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion (C0 xF n v).inclusion.hom.hom.left := (C0 xF n v).closed
  have hTarget : Mono (C0 xF n v).inclusion.hom.hom := Over.mono_of_mono_left _
  refine @CompactSubgroupBaseChange.Construction.exists_compactSubgroupBaseChangeIso _ _ D.nativeIntegralGeometricFrobenius.left _ _ _ _
    (C0 x n v).inclusion (C0 xF n v).inclusion
    (D.pointFrobeniusBlockIso j iota' hsplit x n (labels (v.succ, false))) (O.compact x v)
    ?_ ?_ hSource hTarget
  · intro T z
    exact hC0 x n v T z
  · intro T z
    exact (hC0 xF n v T z).trans (iff_of_eq (congrArg
      (fun b : Bool => if b then True else z = OperatorSpecification.Construction.nativeGroupIdentityPoint
        (CMPointsAt.Construction.l45ChosenBlock j iota' hsplit (D.pointDatum xF.val).data.polarized
          (D.pointDatum xF.val).data.action (labels (v.succ, false)) n) T)
      (D.ordinaryCompact_frobenius j iota' hsplit labels O x v)))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
