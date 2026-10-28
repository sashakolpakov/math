import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoproductSections

/-! # Coproduct Section Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoproductSectionIsomorphism

noncomputable section

/-! The actual sections of a finite coproduct are the finite product of its section modules. -/
open Opposite _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules
universe u

def finiteCoproductSectionsIso {X : Scheme.{u}} {ι : Type u} [Finite ι]
    (M : ι → X.Modules) (U : X.Opens) :
    ModuleCat.of Γ(X, U) Γ(∐ M, U) ≅
      ModuleCat.of Γ(X, U) (∀ i, Γ(M i, U)) := by
  let : HasZeroMorphisms X.Modules := CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  let F : X.Modules ⥤ ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U)) :=
    SheafOfModules.evaluation X.ringCatSheaf (op U)
  let : HasBiproduct M := HasBiproduct.of_hasCoproduct M
  let : F.Additive := by
    constructor
    intro A B f g
    apply ModuleCat.hom_ext
    ext x
    rfl
  let : PreservesFiniteLimits F :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op U)
  let : PreservesLimit (Discrete.functor M) F := by
    infer_instance
  let : PreservesBiproduct M F := preservesBiproduct_of_preservesProduct F
  exact (show F.obj (∐ M) ≅
      ModuleCat.of (X.ringCatSheaf.obj.obj (op U)) (∀ i, F.obj (M i)) from
    F.mapIso (biproduct.isoCoproduct M).symm ≪≫
      F.mapBiproduct M ≪≫ biproduct.isoProduct (F.obj ∘ M) ≪≫ ModuleCat.piIsoPi (F.obj ∘ M))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoproductSectionIsomorphism
