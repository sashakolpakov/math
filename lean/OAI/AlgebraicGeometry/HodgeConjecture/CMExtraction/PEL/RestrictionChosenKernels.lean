import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.RestrictionSubgroups
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.RestrictionKernel

/-! # Restriction Chosen Kernels -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.RestrictionChosenKernels.IsogenyQuotient

noncomputable section

/-! The actual chosen kernel on a restricted correspondence branch is
the original chosen kernel transported by the retained PEL family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {R : Type} [CommRing R] {g N n q : ℕ} [Fact q.Prime]
  {X Y Q Q' T : Scheme}
  (A : AbelianScheme.TateComparison.PEL.PELFamilyData R g N X) (U : AbelianScheme.TateComparison.PEL.PELFamilyData R g N Y)
  (i : X ⟶ Y) (e : AbelianScheme.TateComparison.PELModuli.PELFamilyIso A (U.pullback i))

def restrictionPointFamilyIso (x : T ⟶ X) (x₀ : T ⟶ Y) (h₀ : x₀ = x ≫ i) :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso (A.pullback x) (U.pullback x₀) := by
  subst x₀
  exact RestrictionFiber.IsogenyQuotient.pointFamilyIso A U i e x

variable (r : Q' ⟶ Q) (s t : Q ⟶ Y) (s' t' : Q' ⟶ X)
  (hs : r ≫ s = s' ≫ i) (ht : r ≫ t = t' ≫ i)
  (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (U.pullback s) (U.pullback t) n)
  (χ : R →+* ℤ_[q]) (h : ℕ)
  (c : T ⟶ Q') (x : T ⟶ X) (hx : c ≫ s' = x)
  (c₀ : T ⟶ Q) (x₀ : T ⟶ Y) (hc₀ : c₀ = c ≫ r) (hx₀ : x₀ = x ≫ i)
  (w₀ : c₀ ≫ s = x₀)

include hc₀ in
theorem restrictPELIsogeny_chosen_at_lift :
    ((((AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel (PELRestriction.IsogenyQuotient.restrictPELIsogeny A U i e r s t s' t' hs ht f).isogeny.hom).inf
      (AbelianScheme.TateComparison.Subgroups.splitBlock (A.pullback s') χ h)).pullback c).comapHom
        (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso A.abelian c s' x hx).hom) =
    (((((AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel f.isogeny.hom).inf (AbelianScheme.TateComparison.Subgroups.splitBlock (U.pullback s) χ h)).pullback c₀).comapHom
      (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso U.abelian c₀ s x₀ w₀).hom).comapHom
        (restrictionPointFamilyIso A U i e x x₀ hx₀).abelian.hom) := by
  subst c₀ x₀
  rw [RestrictionKernel.IsogenyQuotient.restrictPELIsogeny_splitKernel]
  have ha := congrArg (fun e => e.hom) (A.pullbackFactor_abelian c s' x hx)
  have hu := congrArg (fun e => e.hom) (U.pullbackFactor_abelian (c ≫ r) s (x ≫ i) w₀)
  have hb := RestrictionSubgroups.IsogenyQuotient.restriction_subgroup_at_lift A U i e r s s' hs c x hx
    ((AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel f.isogeny.hom).inf (AbelianScheme.TateComparison.Subgroups.splitBlock (U.pullback s) χ h))
  apply AbelianScheme.TateComparison.Subgroups.PointSubgroup.ext
  intro V
  ext z
  have hh := congrArg (fun H => z ∈ H.atTest V) hb
  change (z ≫ (A.pullbackFactor c s' x hx).abelian.hom ∈
    (((((AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel f.isogeny.hom).inf (AbelianScheme.TateComparison.Subgroups.splitBlock (U.pullback s) χ h)).pullback r).comapHom
      (PELRestriction.IsogenyQuotient.restrictionFamilyIso A U i e r s s' hs).abelian.hom).pullback c).atTest V) =
    ((z ≫ (RestrictionFiber.IsogenyQuotient.pointFamilyIso A U i e x).abelian.hom) ≫
      (U.pullbackFactor (c ≫ r) s (x ≫ i) w₀).abelian.hom ∈
        (((AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel f.isogeny.hom).inf (AbelianScheme.TateComparison.Subgroups.splitBlock (U.pullback s) χ h)).pullback (c ≫ r)).atTest V) at hh
  rw [ha, hu] at hh
  exact iff_of_eq hh

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.RestrictionChosenKernels.IsogenyQuotient
