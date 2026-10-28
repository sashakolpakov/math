import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothLocalDomain
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineOpenSmooth
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveComponents

/-! # Smooth Projective Decomposition -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme

noncomputable section

/-!
# Finite integral decomposition of arbitrary smooth projective schemes

The local-domain property is proved from smoothness over a field through
the actual affine localization of each stalk. The resulting components
are the genuine open and closed irreducible components, with inherited
smooth complex structure maps and closed projective embeddings.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Set

universe u

/-- Every actual local ring of a scheme smooth over a field is a domain. -/
theorem SmoothProjectiveDecomposition.smoothScheme_stalk_isDomain {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] (x : X) :
    IsDomain (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let := SpecScalarTransport.specSectionScalarAlgebra f U
  let := AffineOpenSmooth.specSectionScalarAlgebra_smooth f U hU
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let := hU.isLocalization_stalk ⟨x, hxU⟩
  let p := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  exact SmoothLocalDomain.isDomain_of_isLocalizationAtPrime_of_smooth K Γ(X, U) (X.presheaf.stalk x) p

/-- In particular, a scheme smooth over a field is reduced. -/
theorem SmoothProjectiveDecomposition.smoothScheme_isReduced {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] : IsReduced X :=
  LocalDomainComponents.isReduced_of_stalkDomains (SmoothProjectiveDecomposition.smoothScheme_stalk_isDomain f)

variable (P : SmoothProjective.SmoothProjectivePresentation)

/-- Smoothness supplies the actual local-domain property required by the
finite irreducible-component construction. -/
theorem SmoothProjective.SmoothProjectivePresentation.stalk_isDomain (x : P.carrier) : IsDomain (P.carrier.presheaf.stalk x) :=
  SmoothProjectiveDecomposition.smoothScheme_stalk_isDomain P.structureMap x

/-- Every smooth projective presentation is reduced, including disconnected
and empty presentations. -/
instance SmoothProjective.SmoothProjectivePresentation.isReduced : IsReduced P.carrier :=
  SmoothProjectiveDecomposition.smoothScheme_isReduced P.structureMap

/-- The genuine irreducible component as an open subset of the original scheme. -/
def SmoothProjective.SmoothProjectivePresentation.componentOpen (C : irreducibleComponents P.carrier) : P.carrier.Opens :=
  P.componentOpenOfStalkDomains P.stalk_isDomain C

@[simp]
theorem SmoothProjective.SmoothProjectivePresentation.componentOpen_coe (C : irreducibleComponents P.carrier) :
    (P.componentOpen C : Set P.carrier) = C.val := rfl

/-- Each irreducible component is itself a genuine integral smooth projective
complex variety. No connectedness, normality, or local-domain assumption is added. -/
def SmoothProjective.SmoothProjectivePresentation.componentVariety (C : irreducibleComponents P.carrier) : IntegralProjective.IntegralProjectiveVariety :=
  P.componentVarietyOfStalkDomains P.stalk_isDomain C

/-- Inclusion of the actual integral component into the original presentation. -/
abbrev SmoothProjective.SmoothProjectivePresentation.componentInclusion (C : irreducibleComponents P.carrier) :
    (P.componentVariety C).carrier ⟶ P.carrier :=
  P.componentInclusionOfStalkDomains P.stalk_isDomain C

instance SmoothProjective.SmoothProjectivePresentation.componentInclusion_isOpenImmersion (C : irreducibleComponents P.carrier) :
    IsOpenImmersion (P.componentInclusion C) :=
  P.componentInclusionOfStalkDomains_isOpenImmersion P.stalk_isDomain C

instance SmoothProjective.SmoothProjectivePresentation.componentInclusion_isClosedImmersion (C : irreducibleComponents P.carrier) :
    IsClosedImmersion (P.componentInclusion C) :=
  P.componentOpenOfStalkDomains_ι_isClosedImmersion P.stalk_isDomain C

/-- The component inclusion respects the given complex structure map. -/
@[reassoc]
theorem SmoothProjective.SmoothProjectivePresentation.componentInclusion_over (C : irreducibleComponents P.carrier) :
    P.componentInclusion C ≫ P.structureMap = (P.componentVariety C).structureMap := rfl

@[simp]
theorem SmoothProjective.SmoothProjectivePresentation.componentInclusion_range (C : irreducibleComponents P.carrier) :
    Set.range (P.componentInclusion C) = C.val :=
  P.componentInclusionOfStalkDomains_range P.stalk_isDomain C

/-- An arbitrary smooth projective presentation is the finite disjoint union
of its actual integral components. -/
def SmoothProjective.SmoothProjectivePresentation.componentCoproductIso :
    (∐ fun C => (P.componentVariety C).carrier) ≅ P.carrier :=
  P.componentCoproductIsoOfStalkDomains P.stalk_isDomain

/-- The coproduct isomorphism carries each summand by its original component
inclusion, supplying the naturality square for restriction to components. -/
@[reassoc (attr := simp)]
theorem SmoothProjective.SmoothProjectivePresentation.componentCoproductIso_ι_hom (C : irreducibleComponents P.carrier) :
    Sigma.ι (fun C => (P.componentVariety C).carrier) C ≫ P.componentCoproductIso.hom =
      P.componentInclusion C := by
  change Sigma.ι (fun C => (P.componentVariety C).carrier) C ≫
    Sigma.desc P.componentInclusion = P.componentInclusion C
  exact Sigma.ι_comp_desc P.componentInclusion C

/-- The component decomposition commutes with the structure map to `Spec ℂ`. -/
@[reassoc]
theorem SmoothProjective.SmoothProjectivePresentation.componentCoproductIso_over :
    P.componentCoproductIso.hom ≫ P.structureMap =
      Sigma.desc (fun C => (P.componentVariety C).structureMap) :=
  P.componentCoproductIsoOfStalkDomains_over P.stalk_isDomain

/-- The same finite component decomposition as an isomorphism over the
complex base, preserving the given scalar structure. -/
def SmoothProjective.SmoothProjectivePresentation.componentCoproductOverIso :
    Over.mk (Sigma.desc (fun C => (P.componentVariety C).structureMap)) ≅ P.toOver :=
  Over.isoMk P.componentCoproductIso P.componentCoproductIso_over

end

end OAI.AlgebraicGeometry.Foundations.Scheme
