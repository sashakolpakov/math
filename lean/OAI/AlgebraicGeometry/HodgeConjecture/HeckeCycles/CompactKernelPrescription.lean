import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CompactKernels

/-! # Compact Kernel Prescription -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CompactKernelPrescription.CM

noncomputable section

/-! Construct NeighborCounting's compact kernel prescription from the actual
ordinary splitting. On multiplicative compact blocks it is the entire
block, and on etale compact blocks it is the identity subgroup.
The required all-test prescription is a proved conclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem compact_image {k : Type} [Field k] {q : ℕ} [Fact q.Prime] (n : ℕ) (b : Bool)
    {G : Grp (Over (Spec (.of k)))}
    (e : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k G q n
      (if b then 3 else 0) (if b then 0 else 3))
    (T : Over (Spec (.of k))) (a : T ⟶ G.X) :
    (∃ h : T ⟶ (AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup e).group.X,
      h ≫ (AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup e).inclusion.hom.hom = a) ↔
    if b then True else a = 1 := by
  cases b with
  | false =>
    change (∃ h : T ⟶ (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q n 0).X,
      h ≫ (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion k e).hom.hom = a) ↔ a = 1
    exact ⟨fun ⟨h, hh⟩ => hh.symm.trans
      (AbelianScheme.FrobeniusKernel.CompactKernels.Construction.ordinaryPureEtale_inclusion_zero k q n e T h),
      fun ha => ⟨1, (MonObj.one_comp _).trans ha.symm⟩⟩
  | true =>
    change (∃ h : T ⟶ (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q n 3).X,
      h ≫ (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion k e).hom.hom = a) ↔ True
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    let i := (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion k e).hom.hom
    exact ⟨a ≫ inv i, by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q)
  {K' : Type} [Field K'] [NumberField K'] {κ' : K' →+* ℂ}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K' κ' q) (iota' : E →+* K') (hsplit : j.HasSplitCoordinates iota')
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (O : D.OrdinaryKernelData j iota' hsplit labels)

def prescription : D.CompactKernelPrescription j iota' hsplit labels :=
  fun x n v => AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup (O.splitting x n v.succ)

theorem prescription_condition :
    D.CompactKernelCondition j iota' hsplit labels O (prescription D j iota' hsplit labels O) := by
  intro x n v T a
  exact compact_image n (O.compact x v) (O.splitting x n v.succ) T a

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CompactKernelPrescription.CM
