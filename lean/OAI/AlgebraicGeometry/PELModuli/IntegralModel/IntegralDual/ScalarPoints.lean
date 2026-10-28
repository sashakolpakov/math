import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.TotalSpace
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.ScalarChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ScalarIntrinsicComparison

/-! # Scalar Points -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Actual source and target dual points on the scalar-changed overlap,
with both projections identified with the original arithmetic relation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R R' : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [CommRing R'] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (π : X ⟶ Q) (φ : R →+* R')

def IntegralAdded.PELId.IntegralAddedPELLevel.scalarDualSourcePoint :
    ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj (U.prescribedDualOverlap π)).left ⟶
      (U.baseChange φ).forgetAuxiliary.data.polarized.dual.abelian.scheme.left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).map
      (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left ≫
    (Relative.ScalarIntrinsicComparison.relativeScalarNativeComparison (Spec.map (CommRingCat.ofHom φ)) X
      U.forgetAuxiliary.data.polarized.dual.abelian.scheme).hom.left

theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarDualSourcePoint_base :
    U.scalarDualSourcePoint π φ ≫ (U.baseChange φ).forgetAuxiliary.data.polarized.dual.abelian.scheme.hom =
      ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).map
        (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection ≫ U.prescribedDualProjection)).left := by
  exact (Category.assoc _ _ _).trans (Relative.ScalarIntrinsicComparison.relativeScalar_point_base _ X _ _)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarDualSourcePoint_fst :
    U.scalarDualSourcePoint π φ ≫ pullback.fst U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom
        (pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ))) =
      pullback.fst (U.prescribedDualOverlap π).hom (Spec.map (CommRingCat.ofHom φ)) ≫
        (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection).left := by
  exact (Category.assoc _ _ _).trans (Relative.ScalarIntrinsicComparison.relativeScalar_point_fst _ X _ _)

variable [NeZero L] [IsReduced X.left] [IsLocallyNoetherian X.left]
    (hU : U.IsFine) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

def IntegralAdded.PELId.IntegralAddedPELLevel.scalarDualTargetPoint :
    ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj (U.prescribedDualOverlap π)).left ⟶
      (U.baseChange φ).forgetAuxiliary.data.polarized.dual.abelian.scheme.left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).map (U.prescribedDualOverlapTarget hU π hk)).left ≫
    (Relative.ScalarIntrinsicComparison.relativeScalarNativeComparison (Spec.map (CommRingCat.ofHom φ)) X
      U.forgetAuxiliary.data.polarized.dual.abelian.scheme).hom.left

theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarDualTargetPoint_base :
    U.scalarDualTargetPoint π φ hU hk ≫ (U.baseChange φ).forgetAuxiliary.data.polarized.dual.abelian.scheme.hom =
      ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).map
        (DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection)).left := by
  have h := (Category.assoc _ _ _).trans
    (Relative.ScalarIntrinsicComparison.relativeScalar_point_base (Spec.map (CommRingCat.ofHom φ)) X
      U.forgetAuxiliary.data.polarized.dual.abelian.scheme (U.prescribedDualOverlapTarget hU π hk))
  exact h.trans (congrArg (fun k => ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).map k).left)
    (U.prescribedDualOverlapTarget_base hU π hk))

theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarDualTargetPoint_fst :
    U.scalarDualTargetPoint π φ hU hk ≫ pullback.fst U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom
        (pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ))) =
      pullback.fst (U.prescribedDualOverlap π).hom (Spec.map (CommRingCat.ofHom φ)) ≫
        (U.prescribedDualOverlapTarget hU π hk).left := by
  exact (Category.assoc _ _ _).trans (Relative.ScalarIntrinsicComparison.relativeScalar_point_fst _ X _ _)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
