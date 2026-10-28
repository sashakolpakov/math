import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PELRestriction
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELKernelTransport

/-! # Restriction Kernel -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.RestrictionKernel.IsogenyQuotient

noncomputable section

/-! Chosen blocks of the transported universal kernel are actual pullbacks
of the original blocks. Finiteness, étaleness, and elementary divisors are
therefore inherited from the full IsogenyQuotient universal isogeny. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] {g N n q : ℕ} [Fact q.Prime]
  {X Y Q Q' : Scheme.{u}}
  (A : AbelianScheme.TateComparison.PEL.PELFamilyData R g N X) (U : AbelianScheme.TateComparison.PEL.PELFamilyData R g N Y)
  (i : X ⟶ Y) (e : AbelianScheme.TateComparison.PELModuli.PELFamilyIso A (U.pullback i))
  (r : Q' ⟶ Q) (s t : Q ⟶ Y) (s' t' : Q' ⟶ X)
  (hs : r ≫ s = s' ≫ i) (ht : r ≫ t = t' ≫ i)
  (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (U.pullback s) (U.pullback t) n)
  (χ : R →+* ℤ_[q]) (h : ℕ)

theorem restrictPELIsogeny_splitKernel :
    (AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel (PELRestriction.IsogenyQuotient.restrictPELIsogeny A U i e r s t s' t' hs ht f).isogeny.hom).inf
      (AbelianScheme.TateComparison.Subgroups.splitBlock (A.pullback s') χ h) =
        (((AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel f.isogeny.hom).inf (AbelianScheme.TateComparison.Subgroups.splitBlock (U.pullback s) χ h)).pullback r).comapHom
          (PELRestriction.IsogenyQuotient.restrictionFamilyIso A U i e r s s' hs).abelian.hom := by
  rw [PELRestriction.IsogenyQuotient.restrictPELIsogeny, AbelianScheme.TateComparison.PELIsogenies.PELIsogeny.splitKernel_transport,
    AbelianScheme.TateComparison.Subgroups.PointSubgroup.pullback_inf, AbelianScheme.TateComparison.Subgroups.PointSubgroup.pullback_kernel, AbelianScheme.TateComparison.SplitSubgroups.splitBlock_pullback]
  rfl

theorem restrictPELIsogeny_splitKernel_geometry (a : Fin 3 → ℕ)
    (hf : ((AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel f.isogeny.hom).inf (AbelianScheme.TateComparison.Subgroups.splitBlock (U.pullback s) χ h)).HasFiniteEtaleModel)
    (ha : ((AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel f.isogeny.hom).inf (AbelianScheme.TateComparison.Subgroups.splitBlock (U.pullback s) χ h)).HasGeometricType q a) :
    ((AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel (PELRestriction.IsogenyQuotient.restrictPELIsogeny A U i e r s t s' t' hs ht f).isogeny.hom).inf
      (AbelianScheme.TateComparison.Subgroups.splitBlock (A.pullback s') χ h)).HasFiniteEtaleModel ∧
    ((AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel (PELRestriction.IsogenyQuotient.restrictPELIsogeny A U i e r s t s' t' hs ht f).isogeny.hom).inf
      (AbelianScheme.TateComparison.Subgroups.splitBlock (A.pullback s') χ h)).HasGeometricType q a := by
  rw [restrictPELIsogeny_splitKernel]
  exact ⟨AbelianScheme.TateComparison.Subgroups.PointSubgroup.hasFiniteEtaleModel_comapIso _
      (AbelianScheme.TateComparison.Subgroups.PointSubgroup.hasFiniteEtaleModel_pullback _ hf r) _,
    AbelianScheme.TateComparison.Subgroups.PointSubgroup.hasGeometricType_comapIso _
      (AbelianScheme.TateComparison.Subgroups.PointSubgroup.hasGeometricType_pullback _ ha r) _⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.RestrictionKernel.IsogenyQuotient
