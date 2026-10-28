import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.Relation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DescentCocycleMap

/-! # Cocycle -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual Poincare product transport is normalized and satisfies
the cocycle law, by its two actual family projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left) (hrigid : U.PrescribedRigid)
include hrigid

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTarget_normalized :
    DescentCocycleChange.DescentCocycle.diagonal π U.prescribedPoincareProjection ≫ U.prescribedPoincareTarget π hU hk =
      𝟙 U.prescribedPoincareSpace := by
  apply U.prescribedPoincare_square.hom_ext
  · exact (DescentCocycleMap.DescentCocycle.normalized_component π U.prescribedPoincareProjection
      U.prescribedDualProjection U.prescribedPoincareDual rfl
      (U.prescribedPoincareTarget π hU hk) (U.prescribedDualOverlapTarget hU π hk)
      (U.prescribedPoincareTarget_dual π hU hk)
      (U.prescribedDualOverlapTarget_normalized hU π hk hrigid)).trans (Category.id_comp _).symm
  · exact (DescentCocycleMap.DescentCocycle.normalized_component π U.prescribedPoincareProjection
      U.prescribedProjection U.prescribedPoincareAbelian U.prescribedPoincareAbelian_projection
      (U.prescribedPoincareTarget π hU hk) (U.prescribedOverlapTarget hU π hk)
      (U.prescribedPoincareTarget_abelian π hU hk)
      (U.prescribedOverlapTarget_normalized hU π hk hrigid)).trans (Category.id_comp _).symm

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTarget_cocycle :
    DescentCocycleChange.DescentCocycle.composition π U.prescribedPoincareProjection (U.prescribedPoincareTarget π hU hk)
      (U.prescribedPoincareTarget_projection π hU hk) ≫ U.prescribedPoincareTarget π hU hk =
      pullback.snd (U.prescribedPoincareTarget π hU hk)
        (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection) ≫ U.prescribedPoincareTarget π hU hk := by
  apply U.prescribedPoincare_square.hom_ext
  · exact DescentCocycleMap.DescentCocycle.cocycle_component π U.prescribedPoincareProjection
      U.prescribedDualProjection U.prescribedPoincareDual rfl
      (U.prescribedPoincareTarget π hU hk) (U.prescribedDualOverlapTarget hU π hk)
      (U.prescribedPoincareTarget_projection π hU hk) (U.prescribedDualOverlapTarget_base hU π hk)
      (U.prescribedPoincareTarget_dual π hU hk)
      (U.prescribedDualOverlapTarget_cocycle hU π hk hrigid)
  · exact DescentCocycleMap.DescentCocycle.cocycle_component π U.prescribedPoincareProjection
      U.prescribedProjection U.prescribedPoincareAbelian U.prescribedPoincareAbelian_projection
      (U.prescribedPoincareTarget π hU hk) (U.prescribedOverlapTarget hU π hk)
      (U.prescribedPoincareTarget_projection π hU hk) (U.prescribedOverlapTarget_base hU π hk)
      (U.prescribedPoincareTarget_abelian π hU hk)
      (U.prescribedOverlapTarget_cocycle hU π hk hrigid)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
