import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointCompactKernelFrobenius
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointActiveSquares
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointPlaneSquare

/-! # Point Chosen Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! Embedded Frobenius pullback isomorphisms for every chosen component
of the independently prescribed Y and Z kernels. -/

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

def Integral.Construction.SplitPELReduction.pointYChosenFrobeniusIso (x : D.OrdinaryPoint) (L : EtaleSubgroups.Construction.ActiveEtaleLine q) : ∀ v : Fin (s + 1),
    (Over.pullback D.nativeIntegralGeometricFrobenius.left).obj
      (D.prescribedYChosen j iota' hsplit labels O C0 x L v).group.X ≅
    (D.prescribedYChosen j iota' hsplit labels O C0 (D.ordinaryFrobenius x)
      (D.pointFrobeniusLineEquiv j iota' hsplit labels O x L) v).group.X :=
  Fin.cases (D.pointFrobeniusLineBaseChangeIso j iota' hsplit labels O x L)
    (fun v => Classical.choose (D.exists_compactKernelFrobeniusIso j iota' hsplit labels O C0 hC0 x 1 v))

theorem Integral.Construction.SplitPELReduction.pointYChosenFrobeniusIso_inclusion (x : D.OrdinaryPoint) (L : EtaleSubgroups.Construction.ActiveEtaleLine q)
    (v : Fin (s + 1)) :
    (D.pointYChosenFrobeniusIso j iota' hsplit labels O C0 hC0 x L v).hom ≫
      (D.prescribedYChosen j iota' hsplit labels O C0 (D.ordinaryFrobenius x)
        (D.pointFrobeniusLineEquiv j iota' hsplit labels O x L) v).inclusion.hom.hom =
    (Over.pullback D.nativeIntegralGeometricFrobenius.left).map
      (D.prescribedYChosen j iota' hsplit labels O C0 x L v).inclusion.hom.hom ≫
      (D.pointFrobeniusBlockIso j iota' hsplit x 1 (labels (v, false))).hom.hom.hom := by
  refine Fin.cases ?_ (fun w => ?_) v
  · exact D.pointFrobeniusLineBaseChangeIso_inclusion j iota' hsplit labels O x L
  · exact Classical.choose_spec
      (D.exists_compactKernelFrobeniusIso j iota' hsplit labels O C0 hC0 x 1 w)

def Integral.Construction.SplitPELReduction.pointZChosenFrobeniusIso (x : D.OrdinaryPoint) : ∀ v : Fin (s + 1),
    (Over.pullback D.nativeIntegralGeometricFrobenius.left).obj
      (D.prescribedZChosen j iota' hsplit labels O C0 x v).group.X ≅
    (D.prescribedZChosen j iota' hsplit labels O C0 (D.ordinaryFrobenius x) v).group.X :=
  Fin.cases (D.pointFrobeniusPlaneBaseChangeIso j iota' hsplit labels O x)
    (fun v => Classical.choose (D.exists_compactKernelFrobeniusIso j iota' hsplit labels O C0 hC0 x 2 v))

theorem Integral.Construction.SplitPELReduction.pointZChosenFrobeniusIso_inclusion (x : D.OrdinaryPoint) (v : Fin (s + 1)) :
    (D.pointZChosenFrobeniusIso j iota' hsplit labels O C0 hC0 x v).hom ≫
      (D.prescribedZChosen j iota' hsplit labels O C0 (D.ordinaryFrobenius x) v).inclusion.hom.hom =
    (Over.pullback D.nativeIntegralGeometricFrobenius.left).map
      (D.prescribedZChosen j iota' hsplit labels O C0 x v).inclusion.hom.hom ≫
      (D.pointFrobeniusBlockIso j iota' hsplit x 2 (labels (v, false))).hom.hom.hom := by
  refine Fin.cases ?_ (fun w => ?_) v
  · exact D.pointFrobeniusPlaneBaseChangeIso_levelTwo j iota' hsplit labels O x
  · exact Classical.choose_spec
      (D.exists_compactKernelFrobeniusIso j iota' hsplit labels O C0 hC0 x 2 w)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
