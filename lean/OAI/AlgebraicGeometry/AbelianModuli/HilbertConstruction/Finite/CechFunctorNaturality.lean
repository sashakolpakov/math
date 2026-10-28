import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CechFunctorComparison

/-! # Cech Functor Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CechFunctorNaturality

noncomputable section

/-! The finite-Cech comparison is natural in the additive functor, in particular for maps between the tensor factors. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
universe u v w uA vA uB vB

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{w} A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B] [HasProducts.{w} B]
variable {T T' : A ⥤ B} [T.Additive] [T'.Additive]
variable [PreservesFiniteProducts T] [PreservesFiniteProducts T']
variable (α : T ⟶ T') (P : Cᵒᵖ ⥤ A) {ι : Type w} [Finite ι] (U : ι → C)

theorem finiteCechFunctorIso_functor_naturality :
    (NatTrans.mapHomologicalComplex α (.up ℕ)).app ((cechComplexFunctor U).obj P) ≫
        (CechFunctorComparison.finiteCechFunctorIso T' P U).hom =
      (CechFunctorComparison.finiteCechFunctorIso T P U).hom ≫ (cechComplexFunctor U).map (Functor.whiskerLeft P α) := by
  apply HomologicalComplex.Hom.ext
  funext n
  let D : (Fin (n + 1) → ι) → A := fun i => P.obj (op (∏ᶜ fun k => U (i k)))
  apply Pi.hom_ext
  intro i
  change Fin (n + 1) → ι at i
  change (α.app (∏ᶜ D) ≫ piComparison T' D) ≫ Pi.π (fun j => T'.obj (D j)) i =
    (piComparison T D ≫ CategoryTheory.Limits.Pi.map (fun j => α.app (D j))) ≫ Pi.π (fun j => T'.obj (D j)) i
  rw [Category.assoc, piComparison_comp_π, ← α.naturality (Pi.π D i),
    Category.assoc, Pi.map_π, ← Category.assoc, piComparison_comp_π]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CechFunctorNaturality
