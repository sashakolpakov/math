import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionComparison
import Mathlib.Topology.Sheaves.Functors

/-! # Section Modules -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionModules

noncomputable section

/-! The tensor comparison as a map of module presheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry

universe u

variable {X P : Scheme.{u}} {R : Type u} [CommRing R]

def inverseImageSectionModules (a : P ⟶ X) (f : R →+* Γ(X, ⊤)) :
    TopCat.Presheaf (ModuleCat.{u} R) X :=
  (TopologicalSpace.Opens.map a.base).op ⋙
    AlgebraSectionModules.algebraSectionModulePresheaf (a.appTop.hom.comp f)

theorem inverseImageSectionModules_isSheaf (a : P ⟶ X) (f : R →+* Γ(X, ⊤)) :
    (inverseImageSectionModules a f).IsSheaf :=
  TopCat.Sheaf.pushforward_sheaf_of_sheaf a.base
    (AlgebraSectionModules.algebraSectionModulePresheaf_isSheaf (a.appTop.hom.comp f))

def tensorSectionModuleComparison (a : P ⟶ X) (f : R →+* Γ(X, ⊤))
    (B : CommAlgCat.{u} R) (q : B →+* Γ(P, ⊤))
    (hq : q.comp (algebraMap R B) = a.appTop.hom.comp f) :
    AlgebraSectionModules.algebraSectionModulePresheaf f ⋙ tensorLeft ((AlgebraSectionModules.commAlgToModules R).obj B) ⟶
      inverseImageSectionModules a f where
  app U := (AlgebraSectionModules.commAlgToModules R).map (SectionComparison.tensorAlgebraSectionComparisonApp a f B q hq U.unop)
  naturality U V h := by
    exact congrArg (fun k => (AlgebraSectionModules.commAlgToModules R).map k)
      ((SectionComparison.tensorAlgebraSectionComparison a f B q hq).naturality h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionModules
