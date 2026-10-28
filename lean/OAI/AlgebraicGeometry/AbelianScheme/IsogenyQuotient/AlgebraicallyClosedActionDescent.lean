import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedHomDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ActionBaseChangeComparison
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Algebraically Closed Action Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedActionDescent.Construction

noncomputable section

/-! The entire integral action descends across extensions of an
algebraically closed ground field. The endomorphism-ring isomorphism
preserves every coefficient and all ring identities simultaneously. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.ActionBaseChangeComparison

variable (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))

set_option backward.isDefEq.respectTransparency false in
theorem algebraicallyClosed_groupEnd_baseChange_bijective :
    Function.Bijective (PELModuli.IntegralModel.Finite.Actions.GroupEndRing.pullback A
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  let u := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let F := Over.pullback u
  have : Surjective u := ⟨Function.surjective_to_subsingleton _⟩
  have : F.Faithful := inferInstance
  constructor
  · intro a b hab
    apply PELModuli.IntegralModel.Finite.Actions.GroupEndRing.ext
    apply F.map_injective
    exact congrArg (PELModuli.IntegralModel.Finite.Actions.GroupEndRing.hom (A.pullback u)) hab
  · intro a
    obtain ⟨f, hf, he⟩ := AbelianModuli.ReferenceFamily.FieldEndomorphismDescent.FieldDescent.field_endomorphism_descends k K A (a.hom (A.pullback u))
    have : IsMonHom f := hf
    refine ⟨PELModuli.IntegralModel.Finite.Actions.GroupEndRing.ofHom A f, ?_⟩
    apply PELModuli.IntegralModel.Finite.Actions.GroupEndRing.ext
    exact he

def algebraicallyClosedGroupEndBaseChangeEquiv :
    PELModuli.IntegralModel.Finite.Actions.GroupEndRing A ≃+* PELModuli.IntegralModel.Finite.Actions.GroupEndRing (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
  RingEquiv.ofBijective (PELModuli.IntegralModel.Finite.Actions.GroupEndRing.pullback A (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (algebraicallyClosed_groupEnd_baseChange_bijective k K A)

variable {R : Type} [CommRing R]

def algebraicallyClosedDescendedAction
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A :=
  PELModuli.IntegralModel.Finite.Actions.integralActionOfRingHom A ((algebraicallyClosedGroupEndBaseChangeEquiv k K A).symm.toRingHom.comp
    (PELModuli.IntegralModel.Finite.Actions.ringHomOfIntegralAction (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ρ))

set_option backward.isDefEq.respectTransparency false in
theorem algebraicallyClosedDescendedAction_recovery
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    (algebraicallyClosedDescendedAction k K A ρ).pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) = ρ := by
  apply PELModuli.IntegralModel.Finite.Actions.integralAction_ext
  intro r
  exact congrArg
    (PELModuli.IntegralModel.Finite.Actions.GroupEndRing.hom (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
    ((algebraicallyClosedGroupEndBaseChangeEquiv k K A).apply_symm_apply
      (PELModuli.IntegralModel.Finite.Actions.GroupEndRing.ofHom _ (ρ.map r)))

set_option backward.isDefEq.respectTransparency false in
theorem algebraicallyClosed_action_of_recovery
    (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K)))
    (e : B.scheme ≅ (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).scheme)
    [IsMonHom e.hom] (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R B) :
    ∃ σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A, ∀ r,
      ρ.map r ≫ e.hom = e.hom ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map (σ.map r) := by
  let τ := PELModuli.IntegralModel.ActionBaseChangeComparison.transportIntegralAction e ρ
  let σ := algebraicallyClosedDescendedAction k K A τ
  have hσ := algebraicallyClosedDescendedAction_recovery k K A τ
  refine ⟨σ, ?_⟩
  intro r
  have hr := congrArg (fun a => a.map r) hσ
  change (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map (σ.map r) =
    e.inv ≫ ρ.map r ≫ e.hom at hr
  rw [hr, e.hom_inv_id_assoc]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedActionDescent.Construction
