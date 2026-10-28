import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldPEL
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldIntrinsicPoincareBundle

/-! # Intrinsic Poincare Bundle PEL -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntrinsicPoincareBundlePEL.ModeledIntrinsic

noncomputable section

/-! The actual modeled PEL isogeny at a prime-power multiplier uses
the accepted original-field PoincareBundle pullback equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldPolarization
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldPEL OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldIntrinsicPoincareBundle.ModeledIntrinsic

variable {E k L : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field k] [Field L] {g N : ℕ} {δ : Fin g → ℕ}
  (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N (Spec (.of k)))
  (a : Spec (.of L) ⟶ Spec (.of k))
  (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.polarized.abelian.scheme (Over.mk a)) (R : F.Model)
  (q h : ℕ) (hq : q.Prime)
  (Q : ModeledAbelian.Lifts.ModeledAbelianQuotient A.polarized.abelian (Over.mk a) F R (q ^ h))
  (hdegree : q.Coprime ((∏ i, δ i) ^ 2))
  (hF :
    let b := AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A.polarized.abelian A.polarized.dual
      A.polarized.polarization (q ^ h) (pow_pos hq.pos h)
    let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.polarized.abelian.scheme (q ^ h)) F
    b.relativeAnnihilator H = H)
  (hlevel : (q ^ h).Coprime N) (hstable : ∀ c, AbelianScheme.IsogenyQuotient.Action.Construction.RelativeSubgroupStable F (A.action.map c))

attribute [local irreducible] ModeledFieldPolarization.modeledFieldDual ModeledFieldPolarization.modeledFieldPolarization

def modeledNativePoincareBundlePELIsogeny :
    AbelianScheme.TateComparison.PELIsogenies.PELIsogeny ((ActionFamilyComparison.Family.actionFamily A).pullback a)
      (ActionFamilyComparison.Family.actionFamily (ModeledFieldPEL.modeledFieldActionData A a F R (q ^ h) (pow_pos hq.pos h) Q
        (hdegree.pow_left h) hF hlevel hstable)) (q ^ h) :=
  { ModeledFieldPEL.modeledFieldPELIsogeny A a F R (q ^ h) (pow_pos hq.pos h) Q
      (hdegree.pow_left h) hF hlevel hstable with
    polarization := FieldIntrinsicPoincareBundle.ModeledIntrinsic.modeledFieldPolarization_acceptedPullback A.polarized a F R q h hq Q hdegree hF }

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntrinsicPoincareBundlePEL.ModeledIntrinsic
