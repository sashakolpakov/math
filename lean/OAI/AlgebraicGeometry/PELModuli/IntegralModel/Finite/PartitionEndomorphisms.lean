import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.PartitionGroupHom
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.EndomorphismEquationBridge

/-! # Partition Endomorphisms -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.PartitionEndomorphisms

noncomputable section

/-! Actual endomorphism rings on a finite disjoint partition of the
parameter base assemble by their geometric restriction maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace FiniteBasePartition
open OAI.AlgebraicGeometry.PELModuli.IntegralModel.EndomorphismEquationBridge.EndomorphismFamilies
variable {S : Scheme.{0}} {I : Type} [Finite I]
    (U : I → Over S) (T : Over S) (j : ∀ i, U i ⟶ T)
    (H : IsColimit (Cofan.mk T.left (fun i => (j i).left)))
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

def restrictionRingHom : Actions.GroupEndRing (A.pullback T.hom) →+*
    ∀ i, Actions.GroupEndRing (A.pullback (U i).hom) := RingHom.pi (fun i => EndomorphismFamiliesId.EndomorphismFamilies.restrict A (j i))

include H in
theorem restrictionRingHom_bijective : Function.Bijective (restrictionRingHom U T j A) := by
  constructor
  · intro r q h
    apply Actions.GroupEndRing.ext
    apply (EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A T).injective
    apply PartitionBaseMaps.FiniteBasePartition.product_hom_ext U T j H A.scheme A.scheme
    intro i
    rw [← EndomorphismHom.EndomorphismFamilies.relativeHom_restrict, ← EndomorphismHom.EndomorphismFamilies.relativeHom_restrict]
    exact congrArg (fun z : Actions.GroupEndRing (A.pullback (U i).hom) =>
      EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A (U i) (z.hom (A.pullback (U i).hom))) (congrFun h i)
  · intro r
    let f (i : I) := EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A (U i) ((r i).hom (A.pullback (U i).hom))
    let q := PartitionBaseMaps.FiniteBasePartition.glue U T j H A.scheme A.scheme f
    have hq := PartitionGroupHom.FiniteBasePartition.glue_respectsGroup U T j H A.scheme f (fun i => EndomorphismEquationBridge.EndomorphismFamilies.relativeHom_group_equations A (U i) (r i))
    let z := EndomorphismEquationBridge.EndomorphismFamilies.groupEndOfFamily A T q hq
    refine ⟨z, funext (fun i => ?_)⟩
    apply Actions.GroupEndRing.ext
    apply (EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A (U i)).injective
    change EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A (U i) ((EndomorphismFamiliesId.EndomorphismFamilies.restrict A (j i) z).hom (A.pullback (U i).hom)) = f i
    rw [EndomorphismHom.EndomorphismFamilies.relativeHom_restrict]
    have hz : EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A T (z.hom (A.pullback T.hom)) = q := EndomorphismEquationBridge.EndomorphismFamilies.groupEndOfFamily_spec A T q hq
    rw [hz]
    exact PartitionBaseMaps.FiniteBasePartition.glue_restrict U T j H A.scheme A.scheme f i

def restrictionRingEquiv : Actions.GroupEndRing (A.pullback T.hom) ≃+*
    ∀ i, Actions.GroupEndRing (A.pullback (U i).hom) :=
  RingEquiv.ofBijective (restrictionRingHom U T j A) (restrictionRingHom_bijective U T j H A)

end FiniteBasePartition

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.PartitionEndomorphisms
