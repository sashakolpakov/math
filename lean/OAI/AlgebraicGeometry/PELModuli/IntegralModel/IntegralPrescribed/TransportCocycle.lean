import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.TransportNormalization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.PointEquations

/-! # Transport Cocycle -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual prescribed-family overlap transport satisfies the
cocycle equation, by naturality and uniqueness of the PEL comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedOverlapTarget_cocycle (hrigid : U.PrescribedRigid) :
    DescentCocycleChange.DescentCocycle.composition π U.prescribedProjection (U.prescribedOverlapTarget hU π hk)
      (U.prescribedOverlapTarget_base hU π hk) ≫ U.prescribedOverlapTarget hU π hk =
      pullback.snd (U.prescribedOverlapTarget hU π hk)
        (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection) ≫ U.prescribedOverlapTarget hU π hk := by
  let a := U.prescribedProjection
  let src := DescentCocycleChange.DescentCocycle.source π a
  let t := U.prescribedOverlapTarget hU π hk
  have ht : t ≫ a = DescentCocycleChange.DescentCocycle.base π a := U.prescribedOverlapTarget_base hU π hk
  let C := Limits.pullback t src
  let k₁ : C ⟶ U.prescribedOverlap π := pullback.fst t src
  let k₂ : C ⟶ U.prescribedOverlap π := pullback.snd t src
  have hs := (IsPullback.of_hasPullback t src).map (Over.forget _)
  have : IsFinite k₁.left := MorphismProperty.of_isPullback hs.flip
    (inferInstanceAs (IsFinite src.left))
  have : Etale k₁.left := MorphismProperty.of_isPullback hs.flip
    (inferInstanceAs (Etale src.left))
  have : IsReduced C.left := Finite.EtaleReduced.finite_etale_isReduced k₁.left
  let f := src ≫ a
  let g := DescentCocycleChange.DescentCocycle.base π a
  have h : f ≫ π = g ≫ π := DescentCocycleChange.DescentCocycle.source_condition π a
  have hb (k : C ⟶ U.prescribedOverlap π) : (k ≫ f) ≫ π = (k ≫ g) ≫ π := by
    simpa only [Category.assoc] using congrArg (fun m => k ≫ m) h
  have hn (k : C ⟶ U.prescribedOverlap π) :
      U.prescribedPointTransport hU π hk (k ≫ f) (k ≫ g) (hb k)
        (k.left ≫ src.left) rfl = k.left ≫ t.left :=
    U.prescribedPointTransport_natural hU π hk hrigid f g h src.left rfl k
  have hmid : k₁ ≫ g = k₂ ≫ f := by
    change k₁ ≫ DescentCocycleChange.DescentCocycle.base π a = k₂ ≫ src ≫ a
    rw [← ht, ← Category.assoc, pullback.condition, Category.assoc]
  have hout : (k₁ ≫ f) ≫ π = (k₂ ≫ g) ≫ π :=
    (hb k₁).trans ((congrArg (fun m => m ≫ π) hmid).trans (hb k₂))
  have hchain := U.prescribedPointTransport_chain hU π hk hrigid
    (k₁ ≫ f) (k₁ ≫ g) (k₂ ≫ f) (k₂ ≫ g) (hb k₁) (hb k₂) hmid hout
    (k₁.left ≫ src.left) (k₂.left ≫ src.left) rfl rfl
    ((hn k₁).trans (congrArg Over.Hom.left (pullback.condition (f := t) (g := src))))
  let c := DescentCocycleChange.DescentCocycle.composition π a t ht
  have hcs : c ≫ src = k₁ ≫ src := DescentCocycleChange.DescentCocycle.composition_source π a t ht
  have hcf : c ≫ f = k₁ ≫ f := by
    change c ≫ src ≫ a = k₁ ≫ src ≫ a
    rw [← Category.assoc, hcs, Category.assoc]
  have hcg : c ≫ g = k₂ ≫ g := DescentCocycleChange.DescentCocycle.composition_base π a t ht
  have hpoints := U.prescribedPointTransport_congr hU π hk
    (c ≫ f) (c ≫ g) (k₁ ≫ f) (k₂ ≫ g) (hb c) hout hcf hcg
    (c.left ≫ src.left) (k₁.left ≫ src.left) rfl rfl (congrArg Over.Hom.left hcs)
  apply Over.OverMorphism.ext
  exact (hn c).symm.trans (hpoints.trans (hchain.trans (hn k₂)))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
