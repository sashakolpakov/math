import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.NormalizedRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.PoincareTripleGeometry

/-! # Line Cocycle -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The constructed normalized Poincare isomorphism satisfies the actual
threefold cocycle equation. Uniqueness is proved on the actual triple
overlap, so no gluing or effectivity assumption enters the equation. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left) (hrigid : U.PrescribedRigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareNormalizedIso_cocycle :
    let src := DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection
    let t := U.prescribedPoincareTarget π hU hk
    let c := DescentCocycleChange.DescentCocycle.composition π U.prescribedPoincareProjection t
      (U.prescribedPoincareTarget_projection π hU hk)
    let k₁ := pullback.fst t src
    let k₂ := pullback.snd t src
    let e := U.prescribedPoincareNormalizedIso hU π hk hrigid
    LineBundle.NormalizedRestriction.lineBundleRestrictIso U.prescribedPoincareLine src.left t.left k₁.left
        (k₁ ≫ src).left (k₂ ≫ src).left rfl (congrArg Over.Hom.left pullback.condition) e ≪≫
      LineBundle.NormalizedRestriction.lineBundleRestrictIso U.prescribedPoincareLine src.left t.left k₂.left
        (k₂ ≫ src).left (k₂ ≫ t).left rfl rfl e =
      LineBundle.NormalizedRestriction.lineBundleRestrictIso U.prescribedPoincareLine src.left t.left c.left
        (k₁ ≫ src).left (k₂ ≫ t).left
        (congrArg Over.Hom.left (DescentCocycleChange.DescentCocycle.composition_source π U.prescribedPoincareProjection t
          (U.prescribedPoincareTarget_projection π hU hk)))
        (congrArg Over.Hom.left (U.prescribedPoincareTarget_cocycle hU π hk hrigid)) e := by
  let src := DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection
  let t := U.prescribedPoincareTarget π hU hk
  let c := DescentCocycleChange.DescentCocycle.composition π U.prescribedPoincareProjection t
    (U.prescribedPoincareTarget_projection π hU hk)
  let k₁ := pullback.fst t src
  let k₂ := pullback.snd t src
  let sd := DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection
  let td := U.prescribedDualOverlapTarget hU π hk
  let cd := DescentCocycleChange.DescentCocycle.composition π U.prescribedDualProjection td
    (U.prescribedDualOverlapTarget_base hU π hk)
  let j₁ := pullback.fst td sd
  let j₂ := pullback.snd td sd
  let w := U.prescribedPoincareTripleZero hU π hk hrigid
  let f := k₁ ≫ src
  let g := k₂ ≫ src
  let h := k₂ ≫ t
  let a := j₁ ≫ sd
  let b := j₂ ≫ sd
  let d := j₂ ≫ td
  have hf : w ≫ f = a ≫ U.prescribedPoincareZero := by
    change w ≫ k₁ ≫ src = (j₁ ≫ sd) ≫ U.prescribedPoincareZero
    rw [← Category.assoc, U.prescribedPoincareTripleZero_fst hU π hk hrigid,
      Category.assoc, U.prescribedPoincareZeroOverlap_source π, Category.assoc]
  have hg : w ≫ g = b ≫ U.prescribedPoincareZero := by
    change w ≫ k₂ ≫ src = (j₂ ≫ sd) ≫ U.prescribedPoincareZero
    rw [← Category.assoc, U.prescribedPoincareTripleZero_snd hU π hk hrigid,
      Category.assoc, U.prescribedPoincareZeroOverlap_source π, Category.assoc]
  have hh : w ≫ h = d ≫ U.prescribedPoincareZero := by
    change w ≫ k₂ ≫ t = (j₂ ≫ td) ≫ U.prescribedPoincareZero
    rw [← Category.assoc, U.prescribedPoincareTripleZero_snd hU π hk hrigid,
      Category.assoc, U.prescribedPoincareZeroOverlap_target hU π hk hrigid, Category.assoc]
  let e := U.prescribedPoincareNormalizedIso hU π hk hrigid
  let e₁ := LineBundle.NormalizedRestriction.lineBundleRestrictIso U.prescribedPoincareLine src.left t.left k₁.left f.left g.left
    rfl (congrArg Over.Hom.left pullback.condition) e
  let e₂ := LineBundle.NormalizedRestriction.lineBundleRestrictIso U.prescribedPoincareLine src.left t.left k₂.left g.left h.left rfl rfl e
  let e₃ := LineBundle.NormalizedRestriction.lineBundleRestrictIso U.prescribedPoincareLine src.left t.left c.left f.left h.left
    (congrArg Over.Hom.left (DescentCocycleChange.DescentCocycle.composition_source π U.prescribedPoincareProjection t
      (U.prescribedPoincareTarget_projection π hU hk)))
    (congrArg Over.Hom.left (U.prescribedPoincareTarget_cocycle hU π hk hrigid)) e
  let F := LineBundle.SquareFrame.lineBundleSquareFrame U.prescribedPoincareLine U.prescribedPoincareZero.left
    U.prescribedPoincareFrame f.left w.left a.left (congrArg Over.Hom.left hf)
  let G := LineBundle.SquareFrame.lineBundleSquareFrame U.prescribedPoincareLine U.prescribedPoincareZero.left
    U.prescribedPoincareFrame g.left w.left b.left (congrArg Over.Hom.left hg)
  let H := LineBundle.SquareFrame.lineBundleSquareFrame U.prescribedPoincareLine U.prescribedPoincareZero.left
    U.prescribedPoincareFrame h.left w.left d.left (congrArg Over.Hom.left hh)
  have he₁ : (Scheme.Modules.pullback w.left).mapIso e₁ ≪≫ G = F :=
    U.prescribedPoincareNormalizedIso_restrict hU π hk hrigid k₁ w j₁
      (U.prescribedPoincareTripleZero_fst hU π hk hrigid) f g a b rfl pullback.condition
      rfl pullback.condition hf hg
  have he₂ : (Scheme.Modules.pullback w.left).mapIso e₂ ≪≫ H = G :=
    U.prescribedPoincareNormalizedIso_restrict hU π hk hrigid k₂ w j₂
      (U.prescribedPoincareTripleZero_snd hU π hk hrigid) g h b d rfl rfl rfl rfl hg hh
  have he₃ : (Scheme.Modules.pullback w.left).mapIso e₃ ≪≫ H = F :=
    U.prescribedPoincareNormalizedIso_restrict hU π hk hrigid c w cd
      (U.prescribedPoincareTripleZero_composition hU π hk hrigid) f h a d
      (DescentCocycleChange.DescentCocycle.composition_source π U.prescribedPoincareProjection t
        (U.prescribedPoincareTarget_projection π hU hk))
      (U.prescribedPoincareTarget_cocycle hU π hk hrigid)
      (DescentCocycleChange.DescentCocycle.composition_source π U.prescribedDualProjection td
        (U.prescribedDualOverlapTarget_base hU π hk))
      (U.prescribedDualOverlapTarget_cocycle hU π hk hrigid) hf hh
  change e₁ ≪≫ e₂ = e₃
  apply Picard.RigidifiedUniqueness.PicardRigidifiedUniqueness.normalizedIso_unique (U.prescribedPoincareTripleDual hU π hk).left w.left
    (congrArg Over.Hom.left (U.prescribedPoincareTripleZero_dual hU π hk hrigid))
    (U.prescribedPoincareTriple_globalFunctions hU π hk hrigid)
    (U.prescribedPoincareLine.pullback f.left).locallyTrivial F H
  · have he : (Scheme.Modules.pullback w.left).mapIso (e₁ ≪≫ e₂) ≪≫ H = F := by
      rw [Functor.mapIso_trans, Iso.trans_assoc, he₂, he₁]
    exact congrArg Iso.hom he
  · exact congrArg Iso.hom he₃

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
