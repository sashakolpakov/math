import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation

/-! # Active Block -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveBlock.Evaluation

noncomputable section

/-! Choose one finite field that splits the original three neighbor
parameters, source q-torsion, and the designated active q-block. Restricting
the same field retains every original parameter label and additionally
supplies the block splitting used for the integral ordinary coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation

variable {K : Type} [Field K] [CharZero K] {g s : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K))) (q : ℕ) [Fact q.Prime]
  (active : Fin s) (multiplicative : Fin s → Bool)
  (p : Fin 3 → Fin s → (A.scheme ⟶ A.scheme)) [∀ i v, IsMonHom (p i v)]
  (p0 : A.scheme ⟶ A.scheme) [IsMonHom p0] (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)

def activeBlockEvaluationSchemes : Option (Option (Fin 3)) → Over (Spec (.of K))
  | none => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1) p0
  | some i => Intrinsic.HeckeEvaluation.neighborEvaluationSchemes A q active multiplicative p hTorsionQuotient i

structure ActiveBlockEvaluation where
  evaluation : Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField K (Intrinsic.HeckeEvaluation.neighborEvaluationSchemes A q active multiplicative p hTorsionQuotient)
  blockCount : ℕ
  blockIso : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of evaluation.carrier)) (ULift (Fin blockCount)) ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K evaluation.carrier)))).obj (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1) p0)

def activeBlockEvaluation : ActiveBlockEvaluation A q active multiplicative p p0 hTorsionQuotient := by
  have htor := AbelianScheme.IsogenyQuotient.Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := A.scheme) (𝟙 (Spec (.of K)))
    q (Fact.out : q.Prime).pos hTorsionQuotient
  have hs := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme_finite_etale A.scheme q htor
  have hblock := AbelianScheme.IsogenyQuotient.Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := A.scheme) (𝟙 (Spec (.of K)))
    (q ^ 1) (pow_pos (Fact.out : q.Prime).pos _) hTorsionQuotient
  have hb := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock_finite_etale (q ^ 1) p0 hblock
  let : ∀ t, IsFinite (activeBlockEvaluationSchemes A q active multiplicative p p0 hTorsionQuotient t).hom :=
    fun t => by
      cases t with
      | none => exact hb.1
      | some t =>
        cases t with
        | none => exact hs.1
        | some i => exact (Intrinsic.HeckeEvaluation.nativeNeighborParameter A q active multiplicative p hTorsionQuotient i).finite
  let : ∀ t, Etale (activeBlockEvaluationSchemes A q active multiplicative p p0 hTorsionQuotient t).hom :=
    fun t => by
      cases t with
      | none => exact hb.2
      | some t =>
        cases t with
        | none => exact hs.2
        | some i => exact (Intrinsic.HeckeEvaluation.nativeNeighborParameter A q active multiplicative p hTorsionQuotient i).etale
  let d := Joint.IntrinsicEvaluation.Lifts.jointFiniteEvaluationField K (activeBlockEvaluationSchemes A q active multiplicative p p0 hTorsionQuotient)
  exact {
    evaluation := {
      carrier := d.carrier
      count := fun i => d.count (some i)
      parameterIso := fun i => d.parameterIso (some i) }
    blockCount := d.count none
    blockIso := d.parameterIso none }

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveBlock.Evaluation
