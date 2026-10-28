import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.Cocycle
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.ZeroTarget
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DescentCocycleMapCartesian

/-! # Triple -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The zero section and dual projection on actual composable Poincare
overlaps, including all projection and composition equations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

abbrev IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTriple := Limits.pullback (U.prescribedPoincareTarget π hU hk)
  (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)

abbrev IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualTriple := Limits.pullback (U.prescribedDualOverlapTarget hU π hk)
  (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTripleDual : U.prescribedPoincareTriple hU π hk ⟶ U.prescribedDualTriple hU π hk :=
  DescentCocycleMap.DescentCocycle.mapComposition π U.prescribedPoincareProjection U.prescribedDualProjection
    U.prescribedPoincareDual rfl (U.prescribedPoincareTarget π hU hk)
    (U.prescribedDualOverlapTarget hU π hk) (U.prescribedPoincareTarget_dual π hU hk)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTripleZero (hrigid : U.PrescribedRigid) :
    U.prescribedDualTriple hU π hk ⟶ U.prescribedPoincareTriple hU π hk :=
  DescentCocycleMap.DescentCocycle.mapComposition π U.prescribedDualProjection U.prescribedPoincareProjection
    U.prescribedPoincareZero U.prescribedPoincareZero_projection (U.prescribedDualOverlapTarget hU π hk)
    (U.prescribedPoincareTarget π hU hk) (U.prescribedPoincareZeroOverlap_target hU π hk hrigid).symm

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTripleZero_fst (hrigid : U.PrescribedRigid) :
    U.prescribedPoincareTripleZero hU π hk hrigid ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ U.prescribedPoincareZeroOverlap π := pullback.lift_fst _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTripleZero_snd (hrigid : U.PrescribedRigid) :
    U.prescribedPoincareTripleZero hU π hk hrigid ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ U.prescribedPoincareZeroOverlap π := pullback.lift_snd _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTripleDual_fst :
    U.prescribedPoincareTripleDual hU π hk ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ U.prescribedPoincareOverlapDual π := pullback.lift_fst _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTripleDual_snd :
    U.prescribedPoincareTripleDual hU π hk ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ U.prescribedPoincareOverlapDual π := pullback.lift_snd _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTripleZero_dual (hrigid : U.PrescribedRigid) :
    U.prescribedPoincareTripleZero hU π hk hrigid ≫ U.prescribedPoincareTripleDual hU π hk = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, U.prescribedPoincareTripleDual_fst, ← Category.assoc,
      U.prescribedPoincareTripleZero_fst hU π hk hrigid, Category.assoc,
      U.prescribedPoincareZeroOverlap_dual π, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, U.prescribedPoincareTripleDual_snd, ← Category.assoc,
      U.prescribedPoincareTripleZero_snd hU π hk hrigid, Category.assoc,
      U.prescribedPoincareZeroOverlap_dual π, Category.comp_id, Category.id_comp]

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTripleZero_composition (hrigid : U.PrescribedRigid) :
    U.prescribedPoincareTripleZero hU π hk hrigid ≫
      DescentCocycleChange.DescentCocycle.composition π U.prescribedPoincareProjection (U.prescribedPoincareTarget π hU hk)
        (U.prescribedPoincareTarget_projection π hU hk) =
    DescentCocycleChange.DescentCocycle.composition π U.prescribedDualProjection (U.prescribedDualOverlapTarget hU π hk)
      (U.prescribedDualOverlapTarget_base hU π hk) ≫ U.prescribedPoincareZeroOverlap π :=
  (DescentCocycleMap.DescentCocycle.composition_map π U.prescribedDualProjection U.prescribedPoincareProjection
    U.prescribedPoincareZero U.prescribedPoincareZero_projection (U.prescribedDualOverlapTarget hU π hk)
    (U.prescribedPoincareTarget π hU hk) (U.prescribedDualOverlapTarget_base hU π hk)
    (U.prescribedPoincareTarget_projection π hU hk)
    (U.prescribedPoincareZeroOverlap_target hU π hk hrigid).symm).symm

omit [NeZero L] [IsReduced X.left] [IsLocallyNoetherian X.left] [IsFinite π.left] [Etale π.left] in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareZero_diagonal :
    U.prescribedPoincareZero ≫ DescentCocycleChange.DescentCocycle.diagonal π U.prescribedPoincareProjection =
      DescentCocycleChange.DescentCocycle.diagonal π U.prescribedDualProjection ≫ U.prescribedPoincareZeroOverlap π :=
  (DescentCocycleMap.DescentCocycle.diagonal_map π U.prescribedDualProjection U.prescribedPoincareProjection
    U.prescribedPoincareZero U.prescribedPoincareZero_projection).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
