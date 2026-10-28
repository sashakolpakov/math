import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldGraphBaseChange
import Mathlib.AlgebraicGeometry.Gluing

/-! # Base Action Separation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseActionSeparation

noncomputable section

/-! Actual endomorphisms and integral actions are determined by their
restrictions to any open covering family of the parameter base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace OpenBaseFamilies

variable {S : Scheme.{0}} {I : Type} (U : I → Over S) (T : Over S)
    (j : ∀ i, U i ⟶ T) [∀ i, IsOpenImmersion (j i).left]
    (hcover : ∀ t : T.left, ∃ i, ∃ u : (U i).left, (j i).left u = t)
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

def familyOpenCover : (A.pullback T.hom).scheme.left.OpenCover where
  I₀ := I
  X i := (A.pullback (U i).hom).scheme.left
  f i := EndomorphismFamiliesId.EndomorphismFamilies.familyMap A (j i)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      obtain ⟨i, u, hu⟩ := hcover ((A.pullback T.hom).scheme.hom x)
      let H := FieldGraphBaseChange.EndomorphismFamilies.familyMap_isPullback A (j i)
      have hx : x ∈ Set.range (pullback.fst (A.pullback T.hom).scheme.hom (j i).left) := by
        rw [Scheme.Pullback.range_fst]
        exact ⟨u, hu⟩
      obtain ⟨z, hz⟩ := hx
      refine ⟨i, H.isoPullback.inv z, ?_⟩
      exact (congrArg (fun f : pullback (A.pullback T.hom).scheme.hom (j i).left ⟶
        (A.pullback T.hom).scheme.left => f z) H.isoPullback_inv_fst).trans hz
    · intro i
      exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
        (FieldGraphBaseChange.EndomorphismFamilies.familyMap_isPullback A (j i)).flip inferInstance

include hcover in
theorem groupEnd_ext_of_open_restrictions
    (r q : Finite.Actions.GroupEndRing (A.pullback T.hom))
    (h : ∀ i, EndomorphismFamiliesId.EndomorphismFamilies.restrict A (j i) r = EndomorphismFamiliesId.EndomorphismFamilies.restrict A (j i) q) : r = q := by
  apply EndomorphismFamiliesId.EndomorphismFamilies.ext_of_fst A
  apply (familyOpenCover U T j hcover A).hom_ext
  intro i
  change EndomorphismFamiliesId.EndomorphismFamilies.familyMap A (j i) ≫ EndomorphismFamiliesId.EndomorphismFamilies.endHom A r ≫ pullback.fst A.scheme.hom T.hom =
    EndomorphismFamiliesId.EndomorphismFamilies.familyMap A (j i) ≫ EndomorphismFamiliesId.EndomorphismFamilies.endHom A q ≫ pullback.fst A.scheme.hom T.hom
  rw [← EndomorphismFamiliesId.EndomorphismFamilies.restrict_fst, ← EndomorphismFamiliesId.EndomorphismFamilies.restrict_fst, h i]

include hcover in
theorem integralAction_ext_of_open_restrictions
    {R : Type} [CommRing R]
    (ρ σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback T.hom))
    (h : ∀ i, Integral.ActionScheme.restrictIntegralAction A ρ (j i) = Integral.ActionScheme.restrictIntegralAction A σ (j i)) : ρ = σ := by
  apply Integral.ActionScheme.ringHomOfIntegralAction_injective
  apply RingHom.ext
  intro r
  apply groupEnd_ext_of_open_restrictions U T j hcover A
  intro i
  exact congrArg (fun τ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback (U i).hom) =>
    Finite.Actions.ringHomOfIntegralAction (A.pullback (U i).hom) τ r) (h i)

end OpenBaseFamilies

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseActionSeparation
