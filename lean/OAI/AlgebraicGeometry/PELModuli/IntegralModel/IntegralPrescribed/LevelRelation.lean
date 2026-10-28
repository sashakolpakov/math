import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.TransportCocycle
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LevelSections

/-! # Level Relation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Every labelled section of the original prescribed full level respects
the actual auxiliary-level equivalence relation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)
    (c : Multiplicative (Fin (2 * (3 * s)) → ZMod N))

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedLevelPoint : X ⟶ U.prescribedTotalSpace :=
  Over.homMk (LevelSections.fullLevelSection U.forgetAuxiliary.data.polarized.level c).left (by
    change _ ≫ (U.forgetAuxiliary.data.polarized.abelian.scheme.hom ≫ X.hom) = X.hom
    rw [← Category.assoc, (LevelSections.fullLevelSection U.forgetAuxiliary.data.polarized.level c).w]
    exact Category.id_comp X.hom)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedLevelPoint_projection :
    U.prescribedLevelPoint c ≫ U.prescribedProjection = 𝟙 X :=
  Over.OverMorphism.ext (LevelSections.fullLevelSection U.forgetAuxiliary.data.polarized.level c).w

variable [NeZero L] [IsReduced X.left] [IsLocallyNoetherian X.left]
    (hU : U.IsFine) (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedLevelOverlap : IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.relation X (3 * s) L ⟶ U.prescribedOverlap π :=
  pullback.lift (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L ≫ U.prescribedLevelPoint c)
    (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU) (by
      rw [Category.assoc, ← Category.assoc (U.prescribedLevelPoint c),
        U.prescribedLevelPoint_projection, Category.id_comp]
      exact Over.OverMorphism.ext hk.w)

omit [IsLocallyNoetherian X.left] [IsFinite π.left] [Etale π.left] in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedLevelOverlap_source :
    U.prescribedLevelOverlap c hU π hk ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedProjection =
      IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L ≫ U.prescribedLevelPoint c := pullback.lift_fst _ _ _

omit [IsLocallyNoetherian X.left] [IsFinite π.left] [Etale π.left] in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedLevelOverlap_base :
    U.prescribedLevelOverlap c hU π hk ≫ DescentCocycleChange.DescentCocycle.base π U.prescribedProjection =
      IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU := pullback.lift_snd _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedLevelOverlap_target (hrigid : U.PrescribedRigid) :
    U.prescribedLevelOverlap c hU π hk ≫ U.prescribedOverlapTarget hU π hk =
      IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU ≫ U.prescribedLevelPoint c := by
  let a := U.prescribedProjection
  let src := DescentCocycleChange.DescentCocycle.source π a
  let f := src ≫ a
  let g := DescentCocycleChange.DescentCocycle.base π a
  let k := U.prescribedLevelOverlap c hU π hk
  let f' := IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L
  let g' := IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU
  have h : f ≫ π = g ≫ π := DescentCocycleChange.DescentCocycle.source_condition π a
  have h' : f' ≫ π = g' ≫ π := Over.OverMorphism.ext hk.w
  have hf : k ≫ f = f' := by
    change k ≫ src ≫ a = f'
    rw [← Category.assoc, U.prescribedLevelOverlap_source, Category.assoc,
      U.prescribedLevelPoint_projection, Category.comp_id]
  have hg : k ≫ g = g' := U.prescribedLevelOverlap_base c hU π hk
  have hn := U.prescribedPointTransport_natural hU π hk hrigid f g h src.left rfl k
  have hx : (f'.left ≫ (U.prescribedLevelPoint c).left) ≫
      U.forgetAuxiliary.data.polarized.abelian.scheme.hom = f'.left := by
    rw [Category.assoc]
    have hw := (LevelSections.fullLevelSection U.forgetAuxiliary.data.polarized.level c).w
    change _ ≫ _ = 𝟙 X.left at hw
    exact (congrArg (fun k => f'.left ≫ k) hw).trans (Category.comp_id f'.left)
  have hpoints := U.prescribedPointTransport_congr hU π hk
    (k ≫ f) (k ≫ g) f' g'
    (by simpa only [Category.assoc] using congrArg (fun m => k ≫ m) h) h' hf hg
    (k.left ≫ src.left) (f'.left ≫ (U.prescribedLevelPoint c).left) rfl hx
    (congrArg Over.Hom.left (U.prescribedLevelOverlap_source c hU π hk))
  have hc := LevelSections.fullLevelSection_transport U.forgetAuxiliary.data.polarized.level f'.left g'.left
    (U.prescribedTransport hU π hk f' g' h').polarized.abelian
    (U.prescribedTransport hU π hk f' g' h').polarized.level c
  apply Over.OverMorphism.ext
  exact hn.symm.trans (hpoints.trans hc)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
