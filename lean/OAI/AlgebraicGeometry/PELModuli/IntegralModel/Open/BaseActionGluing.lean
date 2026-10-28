import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseGroupReflection
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionScheme

/-! # Base Action Gluing -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseActionGluing

noncomputable section

/-! Actual group endomorphisms and entire integral ring actions glue
uniquely on an open base cover from their literal source-overlap equations. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} (C : S.OpenCover) {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem groupEnd_ext_of_open_base_cover (r q : Finite.Actions.GroupEndRing A)
    (h : ∀ i, Finite.Actions.GroupEndRing.pullback A (C.f i) r = Finite.Actions.GroupEndRing.pullback A (C.f i) q) : r = q := by
  apply Finite.Actions.GroupEndRing.ext
  apply BaseGroupReflection.over_hom_ext_of_open_base_cover C
  intro i
  exact congrArg (Finite.Actions.GroupEndRing.hom (A.pullback (C.f i))) (h i)

theorem existsUnique_groupEnd_of_open_base_cover
    (r : ∀ i, Finite.Actions.GroupEndRing (A.pullback (C.f i)))
    (hr : BaseGroupReflection.OpenBaseMorphismCompatible C (fun i => (r i).hom (A.pullback (C.f i)))) :
    ∃! q : Finite.Actions.GroupEndRing A, ∀ i, Finite.Actions.GroupEndRing.pullback A (C.f i) q = r i := by
  obtain ⟨q, hq, _⟩ := BaseGroupReflection.existsUnique_morphism_of_open_base_cover C
    (fun i => (r i).hom (A.pullback (C.f i))) hr
  have : IsMonHom q := BaseGroupReflection.isMonHom_of_open_base_cover C q (fun i => by
    rw [hq i]
    exact inferInstanceAs (IsMonHom ((r i).hom (A.pullback (C.f i)))))
  let a := Finite.Actions.GroupEndRing.ofHom A q
  have ha (i) : Finite.Actions.GroupEndRing.pullback A (C.f i) a = r i := Finite.Actions.GroupEndRing.ext _ (hq i)
  exact ⟨a, ha, fun b hb => groupEnd_ext_of_open_base_cover C A b a
    (fun i => (hb i).trans (ha i).symm)⟩

theorem existsUnique_integralAction_of_open_base_cover
    {R : Type} [CommRing R]
    (ρ : ∀ i, AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback (C.f i)))
    (hρ : ∀ a : R, BaseGroupReflection.OpenBaseMorphismCompatible C (fun i => (ρ i).map a)) :
    ∃! σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A, ∀ i, σ.pullback (C.f i) = ρ i := by
  let r := fun i => Finite.Actions.ringHomOfIntegralAction (A.pullback (C.f i)) (ρ i)
  choose e he _ using fun a : R =>
    existsUnique_groupEnd_of_open_base_cover C A (fun i => r i a) (hρ a)
  let F := fun i => Finite.Actions.GroupEndRing.pullback A (C.f i)
  let ψ : R →+* Finite.Actions.GroupEndRing A :=
    { toFun := e
      map_zero' := by
        apply groupEnd_ext_of_open_base_cover C A
        intro i
        exact (he 0 i).trans ((r i).map_zero.trans (F i).map_zero.symm)
      map_one' := by
        apply groupEnd_ext_of_open_base_cover C A
        intro i
        exact (he 1 i).trans ((r i).map_one.trans (F i).map_one.symm)
      map_add' := by
        intro a b
        apply groupEnd_ext_of_open_base_cover C A
        intro i
        exact (he (a + b) i).trans (((r i).map_add a b).trans
          ((congrArg₂ (· + ·) (he a i).symm (he b i).symm).trans ((F i).map_add _ _).symm))
      map_mul' := by
        intro a b
        apply groupEnd_ext_of_open_base_cover C A
        intro i
        exact (he (a * b) i).trans (((r i).map_mul a b).trans
          ((congrArg₂ (· * ·) (he a i).symm (he b i).symm).trans ((F i).map_mul _ _).symm)) }
  let σ := Finite.Actions.integralActionOfRingHom A ψ
  have hσ (i) : σ.pullback (C.f i) = ρ i := by
    apply Integral.ActionScheme.ringHomOfIntegralAction_injective
    apply RingHom.ext
    intro a
    exact he a i
  refine ⟨σ, hσ, fun τ hτ => ?_⟩
  apply Integral.ActionScheme.ringHomOfIntegralAction_injective
  apply RingHom.ext
  intro a
  apply groupEnd_ext_of_open_base_cover C A
  intro i
  exact congrArg (fun v : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback (C.f i)) =>
    Finite.Actions.ringHomOfIntegralAction (A.pullback (C.f i)) v a) ((hτ i).trans (hσ i).symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseActionGluing
