import OAI.AlgebraicGeometry.Foundations.Scheme.LocalDomainComponents
import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective
import OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective
import Mathlib.AlgebraicGeometry.Limits

/-! # Smooth Projective Components -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme

noncomputable section

/-!
# Integral components once local-domain regularity is established

This file constructs the actual finite disjoint decomposition of a smooth
projective presentation, assuming explicitly that its local rings are
domains. Discharging that local-domain hypothesis from smoothness is a
separate algebraic theorem; this file does not assume it in the definition
of a smooth projective presentation or in a Hodge target.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Set
open scoped Function

variable (P : SmoothProjective.SmoothProjectivePresentation)

/-- A projective presentation has only finitely many irreducible components. -/
instance SmoothProjective.SmoothProjectivePresentation.finite_componentIndex : Finite (irreducibleComponents P.carrier) :=
  (finite_irreducibleComponents_of_isNoetherian (X := P.carrier)).to_subtype

variable (hlocal : ∀ x : P.carrier, IsDomain (P.carrier.presheaf.stalk x))

/-- An irreducible component as its actual open subset, once domain stalks
have established that distinct components are disjoint. -/
def SmoothProjective.SmoothProjectivePresentation.componentOpenOfStalkDomains (C : irreducibleComponents P.carrier) : P.carrier.Opens :=
  ⟨C.val, LocalDomainComponents.isOpen_irreducibleComponent_of_stalkDomains hlocal
    (finite_irreducibleComponents_of_isNoetherian (X := P.carrier)) C.property⟩

@[simp]
theorem SmoothProjective.SmoothProjectivePresentation.componentOpenOfStalkDomains_coe (C : irreducibleComponents P.carrier) :
    (P.componentOpenOfStalkDomains hlocal C : Set P.carrier) = C.val := rfl

/-- The actual open component is integral: it is irreducible and inherits
reducedness, which follows from the domain local rings. -/
instance SmoothProjective.SmoothProjectivePresentation.componentOpenOfStalkDomains_isIntegral (C : irreducibleComponents P.carrier) :
    IsIntegral (P.componentOpenOfStalkDomains hlocal C).toScheme := by
  let : IsReduced P.carrier := LocalDomainComponents.isReduced_of_stalkDomains hlocal
  let : IrreducibleSpace (P.componentOpenOfStalkDomains hlocal C).toScheme :=
    isIrreducible_iff_irreducibleSpace.mp C.property.1
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Inclusion of an open irreducible component is also a closed immersion. -/
instance SmoothProjective.SmoothProjectivePresentation.componentOpenOfStalkDomains_ι_isClosedImmersion
    (C : irreducibleComponents P.carrier) :
    IsClosedImmersion (P.componentOpenOfStalkDomains hlocal C).ι := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι]
  exact isClosed_of_mem_irreducibleComponents C.val C.property

/-- Every component inherits the actual smooth structure map and the actual
closed projective embedding from the original presentation. -/
def SmoothProjective.SmoothProjectivePresentation.componentVarietyOfStalkDomains (C : irreducibleComponents P.carrier) :
    IntegralProjective.IntegralProjectiveVariety :=
  IntegralProjective.IntegralProjectiveVariety.ofClosedImmersion
    ((P.componentOpenOfStalkDomains hlocal C).ι ≫ P.structureMap)
    P.ambientDimension ((P.componentOpenOfStalkDomains hlocal C).ι ≫ P.embedding)
    (by infer_instance)
    (by rw [Category.assoc, P.embedding_over])
    (by infer_instance) (by infer_instance)

/-- The component inclusion is the genuine open-subscheme inclusion. -/
abbrev SmoothProjective.SmoothProjectivePresentation.componentInclusionOfStalkDomains (C : irreducibleComponents P.carrier) :
    (P.componentVarietyOfStalkDomains hlocal C).carrier ⟶ P.carrier :=
  (P.componentOpenOfStalkDomains hlocal C).ι

instance SmoothProjective.SmoothProjectivePresentation.componentInclusionOfStalkDomains_isOpenImmersion
    (C : irreducibleComponents P.carrier) :
    IsOpenImmersion (P.componentInclusionOfStalkDomains hlocal C) := by
  change IsOpenImmersion (P.componentOpenOfStalkDomains hlocal C).ι
  infer_instance

/-- The component inclusion preserves the original complex structure map. -/
@[reassoc]
theorem SmoothProjective.SmoothProjectivePresentation.componentInclusionOfStalkDomains_over (C : irreducibleComponents P.carrier) :
    P.componentInclusionOfStalkDomains hlocal C ≫ P.structureMap =
      (P.componentVarietyOfStalkDomains hlocal C).structureMap := rfl

/-- Its range is exactly the chosen irreducible component. -/
@[simp]
theorem SmoothProjective.SmoothProjectivePresentation.componentInclusionOfStalkDomains_range (C : irreducibleComponents P.carrier) :
    Set.range (P.componentInclusionOfStalkDomains hlocal C) = C.val :=
  (P.componentOpenOfStalkDomains hlocal C).range_ι

/-- The actual component inclusions cover the whole scheme. -/
theorem SmoothProjective.SmoothProjectivePresentation.componentInclusionsOfStalkDomains_iSup :
    (⨆ C, (P.componentInclusionOfStalkDomains hlocal C).opensRange) = ⊤ := by
  apply top_unique
  intro x _
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
  exact ⟨⟨x, mem_irreducibleComponent⟩, rfl⟩

/-- The actual component inclusions have pairwise disjoint ranges. -/
theorem SmoothProjective.SmoothProjectivePresentation.componentInclusionsOfStalkDomains_disjoint :
    Pairwise (Disjoint on
      (fun C => (P.componentInclusionOfStalkDomains hlocal C).opensRange)) := by
  intro C D hCD
  change Disjoint (P.componentInclusionOfStalkDomains hlocal C).opensRange
    (P.componentInclusionOfStalkDomains hlocal D).opensRange
  rw [← TopologicalSpace.Opens.coe_disjoint]
  change Disjoint (Set.range (P.componentInclusionOfStalkDomains hlocal C))
    (Set.range (P.componentInclusionOfStalkDomains hlocal D))
  rw [P.componentInclusionOfStalkDomains_range, P.componentInclusionOfStalkDomains_range]
  exact LocalDomainComponents.irreducibleComponents_disjoint_of_stalkDomains hlocal C.property D.property
    (fun h => hCD (Subtype.ext h))

/-- These genuine integral components exhibit the original scheme as their
categorical disjoint union. -/
theorem SmoothProjective.SmoothProjectivePresentation.componentCofanOfStalkDomains_isColimit :
    Nonempty (IsColimit (Cofan.mk P.carrier (P.componentInclusionOfStalkDomains hlocal))) :=
  AlgebraicGeometry.nonempty_isColimit_cofanMk_of _
    (P.componentInclusionsOfStalkDomains_iSup hlocal)
    (P.componentInclusionsOfStalkDomains_disjoint hlocal)

/-- The canonical finite disjoint-union morphism from the integral components
is an actual scheme isomorphism. -/
def SmoothProjective.SmoothProjectivePresentation.componentCoproductIsoOfStalkDomains :
    (∐ fun C => (P.componentVarietyOfStalkDomains hlocal C).carrier) ≅ P.carrier := by
  letI : IsIso (Sigma.desc (P.componentInclusionOfStalkDomains hlocal)) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
      (Cofan.mk P.carrier (P.componentInclusionOfStalkDomains hlocal))).mp
        (P.componentCofanOfStalkDomains_isColimit hlocal)
  exact asIso (Sigma.desc (P.componentInclusionOfStalkDomains hlocal))

/-- The disjoint-union isomorphism is compatible with the complex base map. -/
@[reassoc]
theorem SmoothProjective.SmoothProjectivePresentation.componentCoproductIsoOfStalkDomains_over :
    (P.componentCoproductIsoOfStalkDomains hlocal).hom ≫ P.structureMap =
      Sigma.desc (fun C => (P.componentVarietyOfStalkDomains hlocal C).structureMap) := by
  apply Sigma.hom_ext
  intro C
  change Sigma.ι (fun C => (P.componentVarietyOfStalkDomains hlocal C).carrier) C ≫
    Sigma.desc (P.componentInclusionOfStalkDomains hlocal) ≫ P.structureMap = _
  rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
  rfl

end

end OAI.AlgebraicGeometry.Foundations.Scheme
