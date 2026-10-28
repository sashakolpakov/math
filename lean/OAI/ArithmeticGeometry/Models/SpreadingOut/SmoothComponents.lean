import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothLocalDomain
import OAI.AlgebraicGeometry.Foundations.Scheme.LocalDomainComponents
import OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Smooth Components -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothComponents.Construction

noncomputable section

/-! Reducedness and the finite integral component decomposition of a smooth
proper scheme over any field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem smooth_scheme_stalk_domain
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] (x : X) :
    IsDomain (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let := OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  have : Algebra.Smooth K Γ(X, U) :=
    (RingHom.Smooth.respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (.of K)).inv (f.appLE ⊤ U le_top)).mpr
        (f.smooth_appLE (isAffineOpen_top (Spec (.of K))) hU le_top)
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  let p := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  exact OAI.AlgebraicGeometry.Foundations.Scheme.SmoothLocalDomain.isDomain_of_isLocalizationAtPrime_of_smooth
    K Γ(X, U) (X.presheaf.stalk x) p

theorem smooth_scheme_reduced
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] : IsReduced X :=
  OAI.AlgebraicGeometry.Foundations.Scheme.LocalDomainComponents.isReduced_of_stalkDomains (smooth_scheme_stalk_domain f)

variable {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] [IsNoetherian X]

def smoothComponentOpen (C : irreducibleComponents X) : X.Opens :=
  ⟨C.val, OAI.AlgebraicGeometry.Foundations.Scheme.LocalDomainComponents.isOpen_irreducibleComponent_of_stalkDomains
    (smooth_scheme_stalk_domain f) finite_irreducibleComponents_of_isNoetherian C.property⟩

theorem smoothComponentOpen_integral (C : irreducibleComponents X) :
    IsIntegral (smoothComponentOpen f C).toScheme := by
  have : IsReduced X := smooth_scheme_reduced f
  have : IrreducibleSpace (smoothComponentOpen f C).toScheme :=
    isIrreducible_iff_irreducibleSpace.mp C.property.1
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem smoothComponentOpen_closedImmersion (C : irreducibleComponents X) :
    IsClosedImmersion (smoothComponentOpen f C).ι := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι]
  exact isClosed_of_mem_irreducibleComponents C.val C.property

theorem smoothComponentOpen_disjoint (C D : irreducibleComponents X) (h : C ≠ D) :
    Disjoint (smoothComponentOpen f C) (smoothComponentOpen f D) := by
  rw [← Opens.coe_disjoint]
  exact OAI.AlgebraicGeometry.Foundations.Scheme.LocalDomainComponents.irreducibleComponents_disjoint_of_stalkDomains
    (smooth_scheme_stalk_domain f) C.property D.property (fun hCD ↦ h (Subtype.ext hCD))

theorem smoothComponentOpen_cover : (⨆ C, smoothComponentOpen f C) = ⊤ := by
  apply top_unique
  intro x _
  apply Opens.mem_iSup.mpr
  exact ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩,
    mem_irreducibleComponent⟩

theorem smoothComponentOpen_smooth_proper [IsProper f] (C : irreducibleComponents X) :
    Smooth ((smoothComponentOpen f C).ι ≫ f) ∧
      IsProper ((smoothComponentOpen f C).ι ≫ f) := by
  have := smoothComponentOpen_closedImmersion f C
  exact ⟨inferInstance, inferInstance⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothComponents.Construction
