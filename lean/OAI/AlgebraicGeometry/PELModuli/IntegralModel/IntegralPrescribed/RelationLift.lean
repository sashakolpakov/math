import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.TransportCocycle

/-! # Relation Lift -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Evaluate the actual descent relation on an arbitrary reduced test. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q T : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedRelation_lift_target (hrigid : U.PrescribedRigid) [IsReduced T.left]
    (x : T ⟶ U.prescribedTotalSpace) (g : T ⟶ X)
    (h : x ≫ (U.prescribedProjection ≫ π) = g ≫ π) :
    (pullback.lift x g h ≫ U.prescribedOverlapTarget hU π hk).left =
      U.prescribedPointTransport hU π hk (x ≫ U.prescribedProjection) g
        (by simpa only [Category.assoc] using h) x.left rfl := by
  let a := U.prescribedProjection
  let src := DescentCocycleChange.DescentCocycle.source π a
  let f₀ := src ≫ a
  let g₀ := DescentCocycleChange.DescentCocycle.base π a
  let k : T ⟶ U.prescribedOverlap π := pullback.lift x g h
  have h₀ : f₀ ≫ π = g₀ ≫ π := DescentCocycleChange.DescentCocycle.source_condition π a
  have hf : k ≫ f₀ = x ≫ a := by
    change k ≫ src ≫ a = x ≫ a
    rw [← Category.assoc, pullback.lift_fst]
  have hg : k ≫ g₀ = g := pullback.lift_snd _ _ _
  have hn := U.prescribedPointTransport_natural hU π hk hrigid f₀ g₀ h₀ src.left rfl k
  have hp := U.prescribedPointTransport_congr hU π hk
    (k ≫ f₀) (k ≫ g₀) (x ≫ a) g
    (by simpa only [Category.assoc] using congrArg (fun m => k ≫ m) h₀)
    (by simpa only [Category.assoc] using h) hf hg
    (k.left ≫ src.left) x.left rfl rfl (congrArg Over.Hom.left (pullback.lift_fst x g h))
  exact hn.symm.trans hp

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedRelation_lift_target_of_base (hrigid : U.PrescribedRigid) [IsReduced T.left]
    (x : T ⟶ U.prescribedTotalSpace) (f g : T ⟶ X)
    (hx : x ≫ U.prescribedProjection = f) (h : f ≫ π = g ≫ π) :
    (pullback.lift x g (by rw [← Category.assoc, hx]; exact h) ≫
      U.prescribedOverlapTarget hU π hk).left =
        U.prescribedPointTransport hU π hk f g h x.left (congrArg Over.Hom.left hx) := by
  have h' : x ≫ (U.prescribedProjection ≫ π) = g ≫ π := by
    rw [← Category.assoc, hx]
    exact h
  exact (U.prescribedRelation_lift_target hU π hk hrigid x g h').trans
    (U.prescribedPointTransport_congr hU π hk (x ≫ U.prescribedProjection) g f g
      (by simpa only [Category.assoc] using h') h hx rfl x.left x.left rfl
      (congrArg Over.Hom.left hx) rfl)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
