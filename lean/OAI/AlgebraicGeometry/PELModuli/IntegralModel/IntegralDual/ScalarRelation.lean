import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.ScalarPoints
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.ScalarTransport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.RelationPoints
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.Point

/-! # Scalar Relation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! On the literal scalar-changed overlap, every compatible PEL
comparison transports the actual source dual point to the actual target. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R R' : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [CommRing R'] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarDualRelation_transport (hrigid : U.PrescribedRigid) (φ : R →+* R')
    [IsReduced ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj (U.prescribedDualOverlap π)).left] :
    let F := Over.pullback (Spec.map (CommRingCat.ofHom φ))
    let f := F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection ≫ U.prescribedDualProjection)
    let g := F.map (DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection)
    ∀ e : PEL.Iso.PolarizedActionIso ((U.baseChange φ).forgetAuxiliary.pullback f).data
        ((U.baseChange φ).forgetAuxiliary.pullback g).data,
      Family.PointBaseChange.FamilyPointTransport.transport (U.baseChange φ).forgetAuxiliary.data.polarized.dual.abelian.scheme
        f.left g.left e.polarized.dual (U.scalarDualSourcePoint π φ) (U.scalarDualSourcePoint_base π φ) =
          U.scalarDualTargetPoint π φ hU hk := by
  let b := Spec.map (CommRingCat.ofHom φ)
  let F := Over.pullback b
  let Z := F.obj (U.prescribedDualOverlap π)
  let a := U.prescribedDualProjection
  let src := DescentCocycleChange.DescentCocycle.source π a
  let f := F.map (src ≫ a)
  let g := F.map (DescentCocycleChange.DescentCocycle.base π a)
  change ∀ e : PEL.Iso.PolarizedActionIso ((U.baseChange φ).forgetAuxiliary.pullback f).data
      ((U.baseChange φ).forgetAuxiliary.pullback g).data,
    Family.PointBaseChange.FamilyPointTransport.transport (U.baseChange φ).forgetAuxiliary.data.polarized.dual.abelian.scheme
      f.left g.left e.polarized.dual (U.scalarDualSourcePoint π φ) (U.scalarDualSourcePoint_base π φ) =
        U.scalarDualTargetPoint π φ hU hk
  intro e
  have hfg : f ≫ F.map π = g ≫ F.map π := by
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map (DescentCocycleChange.DescentCocycle.source_condition π a)
  let adj := Over.mapPullbackAdj b
  let f₀ := (adj.homEquiv Z X).symm f
  let g₀ := (adj.homEquiv Z X).symm g
  let k := (adj.homEquiv Z (U.prescribedDualOverlap π)).symm (𝟙 Z)
  have : IsReduced ((Over.map b).obj Z).left := inferInstanceAs (IsReduced Z.left)
  have h₀ : f₀ ≫ π = g₀ ≫ π :=
    (adj.homEquiv_naturality_right_symm f π).symm.trans
      ((congrArg (adj.homEquiv Z Q).symm hfg).trans
        (adj.homEquiv_naturality_right_symm g π))
  have hf : f₀ = k ≫ (src ≫ a) := by
    simpa only [Category.id_comp] using adj.homEquiv_naturality_right_symm (𝟙 Z) (src ≫ a)
  have hg : g₀ = k ≫ DescentCocycleChange.DescentCocycle.base π a := by
    simpa only [Category.id_comp] using
      adj.homEquiv_naturality_right_symm (𝟙 Z) (DescentCocycleChange.DescentCocycle.base π a)
  have hkl : k.left = pullback.fst (U.prescribedDualOverlap π).hom b := Category.id_comp _
  let x := U.scalarDualSourcePoint π φ
  let y := U.scalarDualTargetPoint π φ hU hk
  let v := pullback.fst X.hom b
  let A := U.forgetAuxiliary.data.polarized.dual.abelian.scheme
  have hx : x ≫ (U.baseChange φ).forgetAuxiliary.data.polarized.dual.abelian.scheme.hom = f.left :=
    U.scalarDualSourcePoint_base π φ
  have hkn : (k ≫ (src ≫ a)) ≫ π = (k ≫ DescentCocycleChange.DescentCocycle.base π a) ≫ π := by
    simpa only [Category.assoc] using congrArg (fun m => k ≫ m) (DescentCocycleChange.DescentCocycle.source_condition π a)
  have hxp : x ≫ pullback.fst A.hom v = k.left ≫ src.left :=
    (U.scalarDualSourcePoint_fst π φ).trans (congrArg (fun j => j ≫ src.left) hkl.symm)
  have hp := U.prescribedDualPointTransport_scalar_fst hU π hk hrigid φ Z f g h₀ e x hx
  have hcmp := U.prescribedDualPointTransport_congr hU π hk f₀ g₀
    (k ≫ (src ≫ a)) (k ≫ DescentCocycleChange.DescentCocycle.base π a) h₀ hkn hf hg
    (x ≫ pullback.fst A.hom v) (k.left ≫ src.left)
    (by rw [Category.assoc, pullback.condition, ← Category.assoc]; exact congrArg (fun j => j ≫ v) hx)
    rfl hxp
  have hn := U.prescribedDualOverlapTarget_natural hU π hk hrigid k
  apply pullback.hom_ext
  · exact hp.trans (hcmp.trans (hn.symm.trans
      ((congrArg (fun j => j ≫ (U.prescribedDualOverlapTarget hU π hk).left) hkl).trans
        (U.scalarDualTargetPoint_fst π φ hU hk).symm)))
  · exact (Family.PointBaseChange.FamilyPointTransport.transport_base _ _ _ _ _ _).trans
      (U.scalarDualTargetPoint_base π φ hU hk).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
