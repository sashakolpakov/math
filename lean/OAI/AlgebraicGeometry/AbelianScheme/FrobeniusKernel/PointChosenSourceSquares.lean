import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointChosenIso
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointBlockEq

/-! # Point Chosen Source Squares -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! The chosen-subgroup inclusion squares written with the same native
source-comparison constructor as the full-kernel theorem. -/

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

theorem Integral.Construction.SplitPELReduction.pointYChosenFrobeniusIso_source_inclusion (x : D.OrdinaryPoint) (L : EtaleSubgroups.Construction.ActiveEtaleLine q)
    (v : Fin (s + 1)) :
    (D.pointYChosenFrobeniusIso j iota' hsplit labels O C0 hC0 x L v).hom ≫
      (D.prescribedYChosen j iota' hsplit labels O C0 (D.ordinaryFrobenius x)
        (D.pointFrobeniusLineEquiv j iota' hsplit labels O x L) v).inclusion.hom.hom =
    (Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of (ModuliPoint.Construction.residueClosure q)))
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q)))).map
      (D.prescribedYChosen j iota' hsplit labels O C0 x L v).inclusion.hom.hom ≫
      (ChosenSourceIso.Construction.frobeniusSourceBlockIso j iota' hsplit (ModuliPoint.Construction.residueClosure q)
        (D.pointDatum x.val).data.polarized.abelian
        (D.pointDatum (D.ordinaryFrobenius x).val).data.polarized.abelian
        (D.pointDatum x.val).data.action (D.pointDatum (D.ordinaryFrobenius x).val).data.action
        (D.ordinaryPointFrobeniusAbelianComparison x) 1 (labels (v, false))).hom.hom.hom := by
  rw [← D.pointFrobeniusBlockIso_eq_source j iota' hsplit x 1 (labels (v, false))]
  exact D.pointYChosenFrobeniusIso_inclusion j iota' hsplit labels O C0 hC0 x L v

theorem Integral.Construction.SplitPELReduction.pointZChosenFrobeniusIso_source_inclusion (x : D.OrdinaryPoint) (v : Fin (s + 1)) :
    (D.pointZChosenFrobeniusIso j iota' hsplit labels O C0 hC0 x v).hom ≫
      (D.prescribedZChosen j iota' hsplit labels O C0 (D.ordinaryFrobenius x) v).inclusion.hom.hom =
    (Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of (ModuliPoint.Construction.residueClosure q)))
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q)))).map
      (D.prescribedZChosen j iota' hsplit labels O C0 x v).inclusion.hom.hom ≫
      (ChosenSourceIso.Construction.frobeniusSourceBlockIso j iota' hsplit (ModuliPoint.Construction.residueClosure q)
        (D.pointDatum x.val).data.polarized.abelian
        (D.pointDatum (D.ordinaryFrobenius x).val).data.polarized.abelian
        (D.pointDatum x.val).data.action (D.pointDatum (D.ordinaryFrobenius x).val).data.action
        (D.ordinaryPointFrobeniusAbelianComparison x) 2 (labels (v, false))).hom.hom.hom := by
  rw [← D.pointFrobeniusBlockIso_eq_source j iota' hsplit x 2 (labels (v, false))]
  exact D.pointZChosenFrobeniusIso_inclusion j iota' hsplit labels O C0 hC0 x v

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
