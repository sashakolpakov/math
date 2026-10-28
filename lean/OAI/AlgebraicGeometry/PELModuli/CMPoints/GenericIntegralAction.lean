import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntegralActionLifting
import OAI.AlgebraicGeometry.PELModuli.CMPoints.GroupMapReflection

/-! # Generic Integral Action -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.GenericIntegralAction

noncomputable section

/-! Restore a full integral action on a smooth arithmetic abelian model
from the finite basis arrows of its generic action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Module
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem groupEndRingPullback_injective
    {S T : Scheme.{0}} [IsReduced S] [IsLocallyNoetherian S]
    (u : T ⟶ S) [IsDominant u] {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) :
    Function.Injective (IntegralModel.Finite.Actions.GroupEndRing.pullback A u) := by
  intro f h heq
  apply IntegralModel.Finite.Actions.GroupEndRing.ext
  apply IntegralModel.GenericIdentities.smooth_hom_eq_of_dominant_base_change u
  exact congrArg (IntegralModel.Finite.Actions.GroupEndRing.hom (A.pullback u)) heq

def genericBasisActionLift
    {S T : Scheme.{0}} [IsReduced S] [IsLocallyNoetherian S]
    (u : T ⟶ S) [IsDominant u] {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    {O : Type*} [CommRing O] {I : Type*} (b : Basis I ℤ O)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O (A.pullback u))
    (v : I → (A.scheme ⟶ A.scheme)) (hv : ∀ i, IsMonHom (v i))
    (hc : ∀ i, (Over.pullback u).map (v i) = ρ.map (b i)) : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A := by
  let w (i : I) : IntegralModel.Finite.Actions.GroupEndRing A :=
    letI := hv i
    IntegralModel.Finite.Actions.GroupEndRing.ofHom A (v i)
  have hw (i : I) : IntegralModel.Finite.Actions.GroupEndRing.pullback A u (w i) =
      IntegralModel.Finite.Actions.ringHomOfIntegralAction (A.pullback u) ρ (b i) := by
    apply IntegralModel.Finite.Actions.GroupEndRing.ext
    exact hc i
  exact IntegralModel.Finite.Actions.integralActionOfRingHom A (IntegralActionLifting.ringActionLiftOfBasis b
    (IntegralModel.Finite.Actions.GroupEndRing.pullback A u) (groupEndRingPullback_injective u A)
    (IntegralModel.Finite.Actions.ringHomOfIntegralAction (A.pullback u) ρ) w hw)

theorem genericBasisActionLift_comparison
    {S T : Scheme.{0}} [IsReduced S] [IsLocallyNoetherian S]
    (u : T ⟶ S) [IsDominant u] {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    {O : Type*} [CommRing O] {I : Type*} (b : Basis I ℤ O)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O (A.pullback u))
    (v : I → (A.scheme ⟶ A.scheme)) (hv : ∀ i, IsMonHom (v i))
    (hc : ∀ i, (Over.pullback u).map (v i) = ρ.map (b i)) :
    (genericBasisActionLift u A b ρ v hv hc).pullback u = ρ := by
  apply IntegralModel.Finite.Actions.integralAction_ext
  intro a
  let w (i : I) : IntegralModel.Finite.Actions.GroupEndRing A :=
    letI := hv i
    IntegralModel.Finite.Actions.GroupEndRing.ofHom A (v i)
  have hw (i : I) : IntegralModel.Finite.Actions.GroupEndRing.pullback A u (w i) =
      IntegralModel.Finite.Actions.ringHomOfIntegralAction (A.pullback u) ρ (b i) := by
    apply IntegralModel.Finite.Actions.GroupEndRing.ext
    exact hc i
  have h := RingHom.congr_fun (IntegralActionLifting.ringActionLiftOfBasis_comparison b
    (IntegralModel.Finite.Actions.GroupEndRing.pullback A u) (groupEndRingPullback_injective u A)
    (IntegralModel.Finite.Actions.ringHomOfIntegralAction (A.pullback u) ρ) w hw) a
  exact congrArg (IntegralModel.Finite.Actions.GroupEndRing.hom (A.pullback u)) h

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.GenericIntegralAction
