import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointChosenSourceSquares
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizedTransport

/-! # Point Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! The independently prescribed full Y and Z kernels commute with
the actual point-data Frobenius on all test schemes, including their
opposite annihilators under the original polarization pairing.
The result types reuse the fully elaborated instances of the proved generic
all-test theorem; their source, target, chosen subgroups and native maps
are supplied explicitly in each declaration. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

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

abbrev Integral.Construction.SplitPELReduction.prescribedFullYKernel_transport (x : D.OrdinaryPoint) (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :=
  PolarizedTransport.Construction.prescribedFullKernel_frobeniusTransport j iota' hsplit
    (D.pointDatum x.val).data (D.pointDatum (D.ordinaryFrobenius x).val).data
    (D.ordinaryPointPolarizedFrobeniusIso x) (D.ordinaryPointFrobeniusAbelianComparison x)
    (D.ordinaryPointFrobeniusAbelianComparison_eq x)
    1 (s + 1) labels (D.prescribedYChosen j iota' hsplit labels O C0 x L)
    (D.prescribedYChosen j iota' hsplit labels O C0 (D.ordinaryFrobenius x)
      (D.pointFrobeniusLineEquiv j iota' hsplit labels O x L))
    (D.pointYChosenFrobeniusIso j iota' hsplit labels O C0 hC0 x L)
    (D.pointYChosenFrobeniusIso_source_inclusion j iota' hsplit labels O C0 hC0 x L)

abbrev Integral.Construction.SplitPELReduction.prescribedFullZKernel_transport (x : D.OrdinaryPoint) :=
  PolarizedTransport.Construction.prescribedFullKernel_frobeniusTransport j iota' hsplit
    (D.pointDatum x.val).data (D.pointDatum (D.ordinaryFrobenius x).val).data
    (D.ordinaryPointPolarizedFrobeniusIso x) (D.ordinaryPointFrobeniusAbelianComparison x)
    (D.ordinaryPointFrobeniusAbelianComparison_eq x)
    2 (s + 1) labels (D.prescribedZChosen j iota' hsplit labels O C0 x)
    (D.prescribedZChosen j iota' hsplit labels O C0 (D.ordinaryFrobenius x))
    (D.pointZChosenFrobeniusIso j iota' hsplit labels O C0 hC0 x)
    (D.pointZChosenFrobeniusIso_source_inclusion j iota' hsplit labels O C0 hC0 x)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
