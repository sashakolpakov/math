import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.PartitionEndomorphisms
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionScheme

/-! # Partition Actions -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.PartitionActions

noncomputable section

/-! Integral actions glue uniquely across a finite disjoint partition
of the base, with the exact geometric restriction maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace FiniteBasePartition
variable {S : Scheme.{0}} {I : Type} [Finite I]
    (U : I → Over S) (T : Over S) (j : ∀ i, U i ⟶ T)
    (H : IsColimit (Cofan.mk T.left (fun i => (j i).left)))
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) {R : Type} [CommRing R]

def glueIntegralAction (ρ : ∀ i, AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback (U i).hom)) :
    AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback T.hom) :=
  Actions.integralActionOfRingHom (A.pullback T.hom)
    ((PartitionEndomorphisms.FiniteBasePartition.restrictionRingEquiv U T j H A).symm.toRingHom.comp
      (RingHom.pi (fun i => Actions.ringHomOfIntegralAction (A.pullback (U i).hom) (ρ i))))

theorem glueIntegralAction_restrict
    (ρ : ∀ i, AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback (U i).hom)) (i : I) :
    Integral.ActionScheme.restrictIntegralAction A (glueIntegralAction U T j H A ρ) (j i) = ρ i := by
  apply Integral.ActionScheme.ringHomOfIntegralAction_injective
  apply RingHom.ext
  intro a
  have h := (PartitionEndomorphisms.FiniteBasePartition.restrictionRingEquiv U T j H A).apply_symm_apply
    (fun i => Actions.ringHomOfIntegralAction (A.pullback (U i).hom) (ρ i) a)
  exact congrFun h i

include H in
theorem integralAction_ext_of_restrictions
    (ρ σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback T.hom))
    (h : ∀ i, Integral.ActionScheme.restrictIntegralAction A ρ (j i) = Integral.ActionScheme.restrictIntegralAction A σ (j i)) : ρ = σ := by
  apply Integral.ActionScheme.ringHomOfIntegralAction_injective
  apply RingHom.ext
  intro a
  apply (PartitionEndomorphisms.FiniteBasePartition.restrictionRingHom_bijective U T j H A).injective
  apply funext
  intro i
  exact congrArg (fun τ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback (U i).hom) =>
    Actions.ringHomOfIntegralAction (A.pullback (U i).hom) τ a) (h i)

include H in
theorem existsUnique_integralAction_glue
    (ρ : ∀ i, AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback (U i).hom)) :
    ∃! σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback T.hom),
      ∀ i, Integral.ActionScheme.restrictIntegralAction A σ (j i) = ρ i := by
  refine ⟨glueIntegralAction U T j H A ρ, glueIntegralAction_restrict U T j H A ρ, ?_⟩
  intro σ hσ
  apply integralAction_ext_of_restrictions U T j H A
  intro i
  exact (hσ i).trans (glueIntegralAction_restrict U T j H A ρ i).symm

end FiniteBasePartition

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.PartitionActions
