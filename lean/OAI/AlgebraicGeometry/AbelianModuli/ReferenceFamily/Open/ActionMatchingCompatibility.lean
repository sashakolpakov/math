import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.ActionMatchingCompatibility

/-! # Action Matching Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ActionMatchingCompatibility

noncomputable section

/-! Matching actual action-functor values imply the literal source-overlap
equations needed for effective gluing. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.ActionMatchingCompatibility
variable {S : Scheme.{0}} (C : S.OpenCover) {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    {R : Type} [CommRing R]
    (ρ : ∀ i, ActionData.IntegralAction R (A.pullback (C.f i)))
    (hmatch : ∀ i j (T : Over S)
      (f : T ⟶ Over.mk (C.f i)) (h : T ⟶ Over.mk (C.f j)),
      PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A (ρ i) f = PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A (ρ j) h)

include hmatch in
theorem openAction_matching_compatible (a : R) :
    PELModuli.IntegralModel.Open.BaseGroupReflection.OpenBaseMorphismCompatible C (fun i => (ρ i).map a) := by
  intro i j
  let T := PELModuli.IntegralModel.Open.ActionMatchingCompatibility.OpenActionOverlap.test C A i j
  let f := PELModuli.IntegralModel.Open.ActionMatchingCompatibility.OpenActionOverlap.testLeft C A i j
  let h := PELModuli.IntegralModel.Open.ActionMatchingCompatibility.OpenActionOverlap.testRight C A i j
  have he := congrArg
    (fun σ : ActionData.IntegralAction R (A.pullback T.hom) => PELModuli.IntegralModel.Finite.Actions.ringHomOfIntegralAction _ σ a)
    (hmatch i j T f h)
  exact PELModuli.IntegralModel.Open.ActionMatchingCompatibility.OpenActionOverlap.endomorphism_equality C A i j
    (PELModuli.IntegralModel.Finite.Actions.ringHomOfIntegralAction (A.pullback (C.f i)) (ρ i) a)
    (PELModuli.IntegralModel.Finite.Actions.ringHomOfIntegralAction (A.pullback (C.f j)) (ρ j) a) he

include hmatch in
theorem existsUnique_action_of_matching :
    ∃! σ : ActionData.IntegralAction R A, ∀ i, σ.pullback (C.f i) = ρ i :=
  PELModuli.IntegralModel.Open.BaseActionGluing.existsUnique_integralAction_of_open_base_cover C A ρ (openAction_matching_compatible C A ρ hmatch)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ActionMatchingCompatibility
