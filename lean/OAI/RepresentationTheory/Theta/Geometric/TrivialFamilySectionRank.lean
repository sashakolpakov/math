import OAI.RepresentationTheory.Theta.Geometric.CechAxisFunctional

/-! # Trivial Family Section Rank -/

namespace OAI.RepresentationTheory.Theta.Geometric.TrivialFamilySectionRank

noncomputable section

/-! A trivial line bundle has one-dimensional global sections over the
base whenever the actual global-function map is an isomorphism. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

def structureBaseSectionsEquiv {X S : Scheme.{u}} (π : X ⟶ S) [IsIso π.appTop] :
    Γ(S, ⊤) ≃ₗ[Γ(S, ⊤)] (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).obj (op ⊤) := by
  let f : Γ(S, ⊤) →ₗ[Γ(S, ⊤)] (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).obj (op ⊤) := {
    toFun := fun x => π.appTop x
    map_add' := π.appTop.hom.map_add
    map_smul' := by
      intro a b
      change π.appTop (a * b) = (X.presheaf.map (𝟙 (op ⊤)) (π.appTop a)) * π.appTop b
      rw [CategoryTheory.Functor.map_id]
      exact π.appTop.hom.map_mul a b }
  exact LinearEquiv.ofBijective f (ConcreteCategory.bijective_of_isIso π.appTop)

def trivialBaseSectionsEquiv {X S : Scheme.{u}} (π : X ⟶ S) [IsIso π.appTop]
    {M : X.Modules} (e : M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :
    (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤) :=
  (((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).mapIso e).app (op ⊤)).toLinearEquiv.trans
    (structureBaseSectionsEquiv π).symm

theorem trivialBaseSections_finrank {X S : Scheme.{u}} (π : X ⟶ S)
    [IsIso π.appTop] [Nontrivial Γ(S, ⊤)] {M : X.Modules} (e : M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :
    Module.finrank Γ(S, ⊤) ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op ⊤)) = 1 :=
  (trivialBaseSectionsEquiv π e).finrank_eq.trans (Module.finrank_self _)

end

end OAI.RepresentationTheory.Theta.Geometric.TrivialFamilySectionRank
