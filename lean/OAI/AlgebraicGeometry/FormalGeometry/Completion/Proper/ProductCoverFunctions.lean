import OAI.AlgebraicGeometry.FormalGeometry.Completion.ChowModificationFunctions
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.CoverModificationSections
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Functions
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ComparisonProperty

/-! # Product Cover Functions -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ProductCoverFunctions.Construction

noncomputable section

/-! Actual formal functions for a finite etale cover of a proper normal factor times an affine base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {K R : Type u} [Field K] [CommRing R] [IsNoetherianRing R]
  {A T : Scheme.{u}} [IsIntegral A]
  (p : A ⟶ Spec (CommRingCat.of K)) [IsProper p]
  (q : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K))
  (t : T ⟶ pullback p q) [IsFinite t] [Etale t]

/-- The original actual formal-functions map is surjective. Its projective cover and all
infinitesimal section isomorphisms are constructed from the proper normal factor. -/
theorem properProductCover_formalFunctionsComparison_surjective
    (hA : ∀ x : A, IsIntegrallyClosed (A.presheaf.stalk x))
    [IsIso (t ≫ pullback.snd p q).appTop] (I : Ideal R) :
    Function.Surjective (FunctionsComparison.Construction.formalFunctionsComparison I (t ≫ pullback.snd p q)) := by
  let D := Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.build p
  let c := D.projection
  have : IsProper c := D.proper
  let a := t ≫ pullback.fst p q
  let f := t ≫ pullback.snd p q
  have : IsIso f.appTop := inferInstanceAs (IsIso (t ≫ pullback.snd p q).appTop)
  let g := pullback.snd c a
  have hc (U : A.Opens) (_hU : IsAffineOpen U) : IsIso (c.app U) :=
    ChowModificationFunctions.Construction.chowModification_app_isIso p hA U
  have : IsProper f := inferInstanceAs (IsProper (t ≫ pullback.snd p q))
  have : IsProper g := inferInstanceAs (IsProper (pullback.snd c a))
  have : Flat (g ≫ f) := Product.CoverModificationSections.Construction.productCover_factorModification_flat p q t c
  have : IsIso g.appTop := Product.CoverModificationSections.Construction.productCover_factorModification_appTop_isIso p q t c hc
  have : IsIso (g ≫ f).appTop := by
    rw [Scheme.Hom.comp_appTop]
    infer_instance
  have : (pullback c a : Scheme.{u}).IsSeparated := by
    constructor
    rw [← terminal.comp_from (g ≫ f)]
    infer_instance
  have : IsAffineHom (pullback.fst p q) := MorphismProperty.pullback_fst _ _ inferInstance
  have : IsAffineHom a := inferInstanceAs (IsAffineHom (t ≫ pullback.fst p q))
  have : IsAffineHom (pullback.fst c a) := MorphismProperty.pullback_fst _ _ inferInstance
  let P := (D.sectionCover.pullback (pullback.fst c a)).projectivePresentation (g ≫ f)
  apply ComparisonDescent.Construction.formalFunctionsComparison_surjective_of_detecting_pullback I f g
  · intro n
    have hi := Product.CoverModificationSections.Construction.productCover_factorModification_infinitesimal_appTop_isIso p q t c hc I n
    exact (ConcreteCategory.isIso_iff_bijective
      (ComparisonDescent.Construction.infinitesimalNeighborhoodMap I f g n).appTop).mp hi |>.injective
  · exact Projective.Functions.Construction.projective_formalFunctionsComparison_surjective (g ≫ f) P I

theorem properProductCover_formalFunctionsComparisonSurjective
    (hA : ∀ x : A, IsIntegrallyClosed (A.presheaf.stalk x))
    [IsIso (t ≫ pullback.snd p q).appTop] (I : Ideal R) :
    ComparisonProperty.Construction.FormalFunctionsComparisonSurjective I (t ≫ pullback.snd p q) :=
  properProductCover_formalFunctionsComparison_surjective p q t hA I

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ProductCoverFunctions.Construction
