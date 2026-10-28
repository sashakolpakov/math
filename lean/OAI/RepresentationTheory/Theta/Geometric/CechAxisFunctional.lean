import OAI.AlgebraicGeometry.FormalGeometry.Completion.BaseSectionPullbackRestriction
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq

/-! # Cech Axis Functional -/

namespace OAI.RepresentationTheory.Theta.Geometric.CechAxisFunctional

noncomputable section

/-! On a Cech chart containing the identity axis, actual restriction
and rigidification define a linear functional on the entire degree-zero
cochain module, before imposing the cocycle condition. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

open OAI.AlgebraicGeometry.FormalGeometry.Completion.BaseSectionPullbackRestriction.Construction

universe u
theorem baseModuleIdTop_smul {S : Scheme.{u}} (M : S.Modules)
    (a : Γ(S, ⊤)) (z : Γ(M, ⊤)) :
    @SMul.smul Γ(S, ⊤) ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (𝟙 S) M).obj (op ⊤)) inferInstance a z = a • z := by
  change (S.presheaf.map (𝟙 (op ⊤)) ((𝟙 S : S ⟶ S).appTop a)) • z = a • z
  rw [CategoryTheory.Functor.map_id, Scheme.Hom.id_appTop]
  rfl

variable {X S : Scheme.{u}} (π : X ⟶ S) (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)

def axisSectionFunctional (W : X.Opens) (hW : (⊤ : S.Opens) ≤ s ⁻¹ᵁ W) :
    (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op W) →ₗ[Γ(S, ⊤)] Γ(S, ⊤) where
  toFun a := r.hom.app ⊤ (AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map s M W ⊤ hW a)
  map_add' a b := by
    have h := (AlgebraicGeometry.FormalGeometry.Completion.BaseSectionPullbackRestriction.Construction.restrictedBaseSectionPullback s π (𝟙 S) (𝟙 S)
      (hs.trans (Category.id_comp (𝟙 S)).symm) M W ⊤ hW).hom.map_add a b
    rw [AlgebraicGeometry.FormalGeometry.Completion.BaseSectionPullbackRestriction.Construction.restrictedBaseSectionPullback_apply, AlgebraicGeometry.FormalGeometry.Completion.BaseSectionPullbackRestriction.Construction.restrictedBaseSectionPullback_apply,
      AlgebraicGeometry.FormalGeometry.Completion.BaseSectionPullbackRestriction.Construction.restrictedBaseSectionPullback_apply] at h
    exact (congrArg (r.hom.app ⊤) h).trans ((r.hom.app ⊤).hom.map_add _ _)
  map_smul' a b := by
    have h := AlgebraicGeometry.FormalGeometry.Completion.BaseSectionPullbackRestriction.Construction.restrictedBaseSectionPullback_smul s π (𝟙 S) (𝟙 S)
      (hs.trans (Category.id_comp (𝟙 S)).symm) M W ⊤ hW a b
    rw [Scheme.Hom.id_appTop] at h
    have h' := h.trans (baseModuleIdTop_smul ((Scheme.Modules.pullback s).obj M) a _)
    exact (congrArg (r.hom.app ⊤) h').trans (r.hom.app_smul a _)

def cechAxisFunctional {I : Type u} [LinearOrder I] (U : I → X.Opens) (i : I)
    (hi : (⊤ : S.Opens) ≤ s ⁻¹ᵁ AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0
      (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i)) :
    (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).X 0 →ₗ[Γ(S, ⊤)] Γ(S, ⊤) :=
  (axisSectionFunctional π s hs M r _ hi).comp
    (Pi.π (fun a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex I 0 => AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 a.1)
      (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i)).hom

end

end OAI.RepresentationTheory.Theta.Geometric.CechAxisFunctional
