import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrescribedBlockSplitting
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointDatumTorsion

/-! # Ordinary Kernel Construction -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.OrdinaryKernelConstruction.CM.OrdinaryConstruction

/-! Construct FrobeniusKernel's entire ordinary source kernel datum from actual
height and Lie-rank conclusions on the original PEL point fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

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

def HasPointLieRank (x : D.OrdinaryPoint) (v : Fin (s + 1)) (d : ℕ) : Prop :=
  AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (D.pointDatum x.val).data.polarized.abelian (D.pointDatum x.val).data.action
    (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota' (labels (v, false))) d

variable
  (hheight : ∀ (x : D.OrdinaryPoint) (v : Fin (s + 1)),
    PELModuli.CMPoints.BlocksProjectors.BlockHasHeight (D.pointDatum x.val).data.polarized.abelian
      (D.pointDatum x.val).data.action (j.localCharacter iota' (labels (v, false))) 3)
  (hactive : ∀ x : D.OrdinaryPoint, HasPointLieRank D j iota' labels x 0 1)
  (hcompact : ∀ (x : D.OrdinaryPoint) (v : Fin s),
    HasPointLieRank D j iota' labels x v.succ 0 ∨ HasPointLieRank D j iota' labels x v.succ 3)

include hcompact in
theorem exists_compact_type (x : D.OrdinaryPoint) (v : Fin s) :
    ∃ b : Bool, HasPointLieRank D j iota' labels x v.succ (if b then 3 else 0) := by
  rcases hcompact x v with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

def compact (x : D.OrdinaryPoint) (v : Fin s) : Bool :=
  Classical.choose (exists_compact_type D j iota' labels hcompact x v)

theorem compact_rank (x : D.OrdinaryPoint) (v : Fin s) :
    HasPointLieRank D j iota' labels x v.succ
      (if OrdinaryConstruction.compact D j iota' labels hcompact x v then 3 else 0) :=
  Classical.choose_spec (exists_compact_type D j iota' labels hcompact x v)

def kernelData : D.OrdinaryKernelData j iota' hsplit labels := by
  let c := OrdinaryConstruction.compact D j iota' labels hcompact
  refine { compact := c, splitting := fun x n v => ?_ }
  have hr (v : Fin (s + 1)) : HasPointLieRank D j iota' labels x v (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45MultiplicativeHeights (c x) v) := by
    refine Fin.cases (hactive x) (fun w => ?_) v
    exact compact_rank D j iota' labels hcompact x w
  have he (v : Fin (s + 1)) :
      3 - AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45MultiplicativeHeights (c x) v = AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45EtaleHeights (c x) v := by
    refine Fin.cases rfl (fun w => ?_) v
    change 3 - (if c x w then 3 else 0) = if c x w then 0 else 3
    cases c x w <;> rfl
  have ho := (D.isOrdinary_iff_pointDatum_count x.val).mp x.property
  have h := PrescribedBlockSplitting.CM.splitting j iota' hsplit
    (D.pointDatum x.val).data.polarized (D.pointDatum x.val).data.action (labels (v, false))
    3 (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45MultiplicativeHeights (c x) v) ho (hheight x v) (hr v) n
  rw [he v] at h
  exact Classical.choice h

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.OrdinaryKernelConstruction.CM.OrdinaryConstruction

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.OrdinaryKernelConstruction.CM.PositiveData

/-! Express FrobeniusKernel's successor-indexed kernel datum at an arbitrary
positive dimension by equality transport, preserving the entire source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q)
  {K' : Type} [Field K'] [NumberField K'] {κ' : K' →+* ℂ}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K' κ' q) (iota' : E →+* K') (hsplit : j.HasSplitCoordinates iota')
  (labels : (Fin s × Bool) ≃ Gal(E/ℚ))

def KernelDataAt (n : ℕ) (hs : s = n + 1) : Type := by
  subst s
  exact D.OrdinaryKernelData j iota' hsplit labels

theorem construct (n : ℕ) (hs : s = n + 1)
    (hheight : ∀ (x : D.OrdinaryPoint) (v : Fin s),
      PELModuli.CMPoints.BlocksProjectors.BlockHasHeight (D.pointDatum x.val).data.polarized.abelian
        (D.pointDatum x.val).data.action (j.localCharacter iota' (labels (v, false))) 3)
    (hactive : ∀ x : D.OrdinaryPoint,
      AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (D.pointDatum x.val).data.polarized.abelian (D.pointDatum x.val).data.action
        (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota' (labels (⟨0, by omega⟩, false))) 1)
    (hcompact : ∀ (x : D.OrdinaryPoint) (v : Fin s), v.val ≠ 0 →
      AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (D.pointDatum x.val).data.polarized.abelian (D.pointDatum x.val).data.action
        (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota' (labels (v, false))) 0 ∨
      AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (D.pointDatum x.val).data.polarized.abelian (D.pointDatum x.val).data.action
        (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota' (labels (v, false))) 3) :
    Nonempty (KernelDataAt D j iota' hsplit labels n hs) := by
  subst s
  exact ⟨OrdinaryConstruction.kernelData D j iota' hsplit labels
    hheight hactive (fun x v => hcompact x v.succ (Nat.succ_ne_zero v.val))⟩

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.OrdinaryKernelConstruction.CM.PositiveData

end

end OAI
