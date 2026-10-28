import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReducedCorrespondence
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CorrespondenceFibers

/-! # Multiset Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.MultisetTransport

noncomputable section

/-! Restriction and base change preserve complete endpoint multisets.
The reindexing counts each source-fiber branch once and retains repeated
targets, so a native raw-Hecke multiset identity transfers unchanged. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction

universe u
variable {B B' : Scheme.{u}} (p : B' ⟶ B) (M : Over B)
  {X : Over B'} [IsReduced X.left] [IsLocallyNoetherian X.left]
  (e : X ≅ (Over.pullback p).obj (PELModuli.IntegralModel.Reduction.reduction M))
  (C : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M) {T : Over B'} (x : T ⟶ X)
  [Finite (C.Fiber (ReducedCorrespondence.IsogenyQuotient.originalModelPoint p M e x))]

theorem model_endpoint_multiset :
    letI : Finite ((ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).Fiber x) :=
      Finite.of_equiv _ (ReducedCorrespondence.IsogenyQuotient.modelFiberEquiv p M e C x).symm
    AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction.finiteTargetMultiset (fun z : (ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).Fiber x =>
      ReducedCorrespondence.IsogenyQuotient.originalModelPoint p M e ((ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).endpoint z)) =
      AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction.finiteTargetMultiset (fun z : C.Fiber (ReducedCorrespondence.IsogenyQuotient.originalModelPoint p M e x) => C.endpoint z) := by
  let : Finite ((ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).Fiber x) :=
    Finite.of_equiv _ (ReducedCorrespondence.IsogenyQuotient.modelFiberEquiv p M e C x).symm
  rw [AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction.finiteTargetMultiset_reindex (ReducedCorrespondence.IsogenyQuotient.modelFiberEquiv p M e C x)]
  congr 1
  funext z
  exact (ReducedCorrespondence.IsogenyQuotient.modelFiberEquiv_endpoint p M e C x ((ReducedCorrespondence.IsogenyQuotient.modelFiberEquiv p M e C x).symm z)).trans
    (congrArg C.endpoint ((ReducedCorrespondence.IsogenyQuotient.modelFiberEquiv p M e C x).apply_symm_apply z))

theorem model_raw_multiset (raw : Multiset (Over.mk (T.hom ≫ p) ⟶ M))
    (hraw : AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction.finiteTargetMultiset (fun z : C.Fiber (ReducedCorrespondence.IsogenyQuotient.originalModelPoint p M e x) => C.endpoint z) = raw) :
    letI : Finite ((ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).Fiber x) :=
      Finite.of_equiv _ (ReducedCorrespondence.IsogenyQuotient.modelFiberEquiv p M e C x).symm
    AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction.finiteTargetMultiset (fun z : (ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).Fiber x =>
      ReducedCorrespondence.IsogenyQuotient.originalModelPoint p M e ((ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).endpoint z)) = raw :=
  (model_endpoint_multiset p M e C x).trans hraw

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.MultisetTransport
