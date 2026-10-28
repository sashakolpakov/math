import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescriptionCongruence

/-! # Prescribed Compact Kernels -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! The literal whole/identity compact prescription agrees on every test
with the multiplicative subgroup of the supplied ordinary splitting. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] {q : ℕ} [Fact q.Prime]

theorem PrescribedCompactKernels.Construction.ordinaryCompactMultiplicative_image {G : Grp (Over (Spec (.of k)))}
    (n : ℕ) (b : Bool)
    (e : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k G q n (if b then 3 else 0) (if b then 0 else 3))
    (T : Over (Spec (.of k))) (a : T ⟶ G.X) :
    (∃ h : T ⟶ (FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup e).group.X,
      h ≫ (FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup e).inclusion.hom.hom = a) ↔
      if b then True else a = 1 := by
  cases b with
  | false =>
    change (∃ h : T ⟶ (OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q n 0).X,
      h ≫ (OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion k e).hom.hom = a) ↔ a = 1
    constructor
    · rintro ⟨h, hh⟩
      exact hh.symm.trans (CompactKernels.Construction.ordinaryPureEtale_inclusion_zero k q n e T h)
    · intro ha
      exact ⟨1, (MonObj.one_comp _).trans ha.symm⟩
  | true =>
    change (∃ h : T ⟶ (OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q n 3).X,
      h ≫ (OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion k e).hom.hom = a) ↔ True
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    let i := (OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion k e).hom.hom
    exact ⟨a ≫ inv i, by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩

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
theorem Integral.Construction.SplitPELReduction.compactPrescription_multiplicative (x : D.OrdinaryPoint) (n : ℕ) (v : Fin s)
    (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (CMPointsAt.Construction.l45ChosenBlock j iota' hsplit (D.pointDatum x.val).data.polarized
      (D.pointDatum x.val).data.action (labels (v.succ, false)) n).X) :
    (∃ h : T ⟶ (C0 x n v).group.X, h ≫ (C0 x n v).inclusion.hom.hom = a) ↔
    (∃ h : T ⟶ (FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup (O.splitting x n v.succ)).group.X,
      h ≫ (FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup (O.splitting x n v.succ)).inclusion.hom.hom = a) :=
  (hC0 x n v T a).trans
    (PrescribedCompactKernels.Construction.ordinaryCompactMultiplicative_image n (O.compact x v) (O.splitting x n v.succ) T a).symm

include hC0 in
theorem Integral.Construction.SplitPELReduction.prescribedFullXKernel_multiplicative (x : D.OrdinaryPoint)
    (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme) :
    D.prescribedFullXKernel j iota' hsplit labels O C0 x T a ↔
      Prescription.Construction.prescribedFullKernel j iota' hsplit (D.pointDatum x.val).data.polarized
        (D.pointDatum x.val).data.action 1 (s + 1) labels
        (fun v => FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup (O.splitting x 1 v)) T a := by
  apply PrescriptionCongruence.Construction.prescribedFullKernel_congr
  intro v
  refine Fin.cases ?_ (fun w => ?_) v
  · intro T a
    rfl
  · exact D.compactPrescription_multiplicative j iota' hsplit labels O C0 hC0 x 1 w

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
