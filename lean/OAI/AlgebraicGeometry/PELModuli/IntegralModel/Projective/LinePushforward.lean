import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.TypeFromAffineRestrictions
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.QuasicoherentPushforward
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.SectionFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.FiberProjectivity
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardSections

/-! # Line Pushforward -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.LinePushforward

noncomputable section

/-! Proper morphisms equipped with a relatively ample line bundle send
actual line bundles to coherent modules over locally noetherian bases. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem lineBundlePushforward_finiteType_of_relativelyAmple
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (H : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hH : H.IsRelativelyAmple f)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : ((pushforward f).obj L.sheaf).IsFiniteType := by
  have : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  have : ((pushforward f).obj L.sheaf).IsQuasicoherent :=
    QuasicoherentPushforward.quasicoherent_pushforward_of_quasiCompact_separated f L.sheaf
  apply IntegralModel.Finite.TypeFromAffineRestrictions.finiteType_of_affine_restriction_sections_finite
  intro U
  have : IsAffine U.1.toScheme := U.2
  have : IsLocallyNoetherian U.1.toScheme := inferInstance
  have : IsNoetherianRing Γ(U.1.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let V := f ⁻¹ᵁ U.1
  let fU := f ∣_ U.1
  let P := hH.localProjectivePresentation U.1 U.2
  let LU := L.pullback V.ι
  have : LU.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent LU
  have : LU.sheaf.IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation LU
  have : LU.sheaf.IsFiniteType := by
    obtain ⟨p, hp⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData LU.sheaf
    refine { exists_localGeneratorsData := ⟨p.localGeneratorsData, ?_⟩ }
    constructor
    intro i
    exact (hp.isFinite_presentation i).isFiniteType_generators
  have : Module.Finite Γ(U.1.toScheme, ⊤) ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor fU).obj LU.sheaf) :=
    SectionFiniteness.projectivePresentation_globalSections_finite (Over.mk fU) P LU.sheaf
  have : Module.Finite Γ(U.1.toScheme, ⊤)
      ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (fU ≫ 𝟙 U.1.toScheme)).obj LU.sheaf) := by
    let k : (SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor fU).obj LU.sheaf →ₗ[Γ(U.1.toScheme, ⊤)]
        (SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (fU ≫ 𝟙 U.1.toScheme)).obj LU.sheaf := {
      toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact Module.Finite.of_surjective k Function.surjective_id
  have : Module.Finite Γ(U.1.toScheme, ⊤)
      ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (𝟙 U.1.toScheme)).obj ((pushforward fU).obj LU.sheaf)) :=
    Module.Finite.equiv
      (ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardSections.Construction.baseGlobalSectionsPushforwardEquiv fU (𝟙 U.1.toScheme) LU.sheaf).symm
  have : Module.Finite Γ(U.1.toScheme, ⊤) Γ((pushforward fU).obj LU.sheaf, ⊤) := by
    let k : (SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (𝟙 U.1.toScheme)).obj ((pushforward fU).obj LU.sheaf)
        →ₗ[Γ(U.1.toScheme, ⊤)] Γ((pushforward fU).obj LU.sheaf, ⊤) := {
      toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact Module.Finite.of_surjective k Function.surjective_id
  let e : (((pushforward f).obj L.sheaf).restrict U.1.ι) ≅
      (pushforward fU).obj LU.sheaf :=
    SheafCohomology.Projective.ModuleRestrictPushforward.Scheme.Modules.restrictPushforwardIsoOfIsPullbackApp f fU V.ι U.1.ι
      (isPullback_morphismRestrict f U.1) L.sheaf ≪≫
      (pushforward fU).mapIso ((restrictFunctorIsoPullback V.ι).app L.sheaf)
  let eΓ := (SheafOfModules.evaluation U.1.toScheme.ringCatSheaf (op ⊤)).mapIso e
  let k : Γ((pushforward fU).obj LU.sheaf, ⊤) →ₗ[Γ(U.1.toScheme, ⊤)]
      Γ(((pushforward f).obj L.sheaf).restrict U.1.ι, ⊤) := {
    toFun := eΓ.inv
    map_add' := eΓ.inv.hom.map_add
    map_smul' := eΓ.inv.hom.map_smul }
  exact Module.Finite.of_surjective k (ConcreteCategory.bijective_of_isIso eΓ.inv).surjective

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.LinePushforward
