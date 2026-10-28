import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldPolarization
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.RosatiCondition
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison

/-! # Modeled Field PEL -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldPEL

noncomputable section

/-! Assemble the positive modeled quotient, its actual integral action,
Rosati condition, normalized Poincare comparison, and every ordered level
marking into the native PEL isogeny interface. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldPolarization
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family

variable {E k L : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field k] [Field L] {g N : ℕ} {δ : Fin g → ℕ}
  (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N (Spec (.of k)))
  (a : Spec (.of L) ⟶ Spec (.of k))
  (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.polarized.abelian.scheme (Over.mk a)) (R : F.Model)
  (n : ℕ) (hn : 0 < n)
  (Q : ModeledAbelian.Lifts.ModeledAbelianQuotient A.polarized.abelian (Over.mk a) F R n)
  (hdegree : n.Coprime ((∏ i, δ i) ^ 2))
  (hF :
    let b := AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A.polarized.abelian A.polarized.dual
      A.polarized.polarization n hn
    let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.polarized.abelian.scheme n) F
    b.relativeAnnihilator H = H)
  (hlevel : n.Coprime N) (hstable : ∀ c, AbelianScheme.IsogenyQuotient.Action.Construction.RelativeSubgroupStable F (A.action.map c))

def modeledFieldActionData : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N (Spec (.of L)) where
  polarized := ModeledFieldPolarization.modeledFieldPolarized A.polarized a F R n hn Q hdegree hF hlevel
  action := Q.action A.action hstable

omit [Algebra ℚ E] in
theorem modeledFieldActionData_rosati (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A.polarized A.action) :
    AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation
      (modeledFieldActionData A a F R n hn Q hdegree hF hlevel hstable).polarized
      (modeledFieldActionData A a F R n hn Q hdegree hF hlevel hstable).action :=
  FieldQuotient.RosatiCondition.quotient_rosati (A.polarized.pullback a)
    (ModeledFieldPolarization.modeledFieldPolarized A.polarized a F R n hn Q hdegree hF hlevel) Q.isogeny
    (A.action.pullback a) (Q.action A.action hstable)
    (fun c => (Q.action_projection A.action hstable c).symm) n
    (ModeledFieldPolarization.modeledFieldPolarization_nativePullback A.polarized a F R n hn Q hdegree hF)
    (PELModuli.IntegralModel.PEL.BaseChange.rosati_pullback A.polarized A.action hρ a)

def modeledFieldPELIsogeny :
    AbelianScheme.TateComparison.PELIsogenies.PELIsogeny ((ActionFamilyComparison.Family.actionFamily A).pullback a)
      (ActionFamilyComparison.Family.actionFamily (modeledFieldActionData A a F R n hn Q hdegree hF hlevel hstable)) n where
  isogeny := Q.isogeny
  dualHom := AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap Q.isogeny.hom (A.polarized.dual.pullback a)
    (ModeledFieldPolarization.modeledFieldDual A.polarized a F R n hn Q)
  dualGroup := NeighborCounting.Field.PoincarePullback.nativeDualMap_isMonHom
    (A.polarized.dual.pullback a) (ModeledFieldPolarization.modeledFieldDual A.polarized a F R n hn Q) Q.isogeny.hom
  poincare := (NeighborCounting.Field.PoincarePullback.nativeDualMap_poincare
    (A.polarized.dual.pullback a) (ModeledFieldPolarization.modeledFieldDual A.polarized a F R n hn Q) Q.isogeny.hom).symm
  equivariant c := by
    rw [AbelianScheme.TateComparison.PEL.PELFamilyData.pullback_action_schemeMap]
    change (Over.pullback a).map (AbelianScheme.TateComparison.End.endSchemeMap A.polarized.abelian.scheme
      ((AbelianScheme.TateComparison.PELAdapters.actionToEnd A.action) c)) ≫ Q.isogeny.hom =
        Q.isogeny.hom ≫ AbelianScheme.TateComparison.End.endSchemeMap Q.target.scheme ((AbelianScheme.TateComparison.PELAdapters.actionToEnd (Q.action A.action hstable)) c)
    rw [AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap, AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap]
    exact (Q.action_projection A.action hstable c).symm
  polarization := ModeledFieldPolarization.modeledFieldPolarization_nativePullback A.polarized a F R n hn Q hdegree hF
  marking T c := (Q.level_projection N hlevel (A.polarized.pullback a).level T c).symm

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldPEL
