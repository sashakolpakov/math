import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId

/-! # Ordinary De Rham Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryDeRhamFunctor.Ordinary

noncomputable section

/-!
# IntegralComparison: functoriality of the actual ordinary de Rham complexes
-/

open _root_.CategoryTheory

universe u

variable {R : Type u} [CommRing R]

def map {A B : CommAlgCat.{u} R} (f : A ⟶ B) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A ⟶ AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R B where
  f i := ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f i)
  comm' i j hij := by
    change i + 1 = j at hij
    subst j
    dsimp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    exact LinearMap.ext (fun ω => (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_differential f i ω).symm)

theorem map_id (A : CommAlgCat.{u} R) : Ordinary.map (𝟙 A) = 𝟙 (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  exact LinearMap.ext (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_id A i)

theorem map_comp {A B C : CommAlgCat.{u} R} (f : A ⟶ B) (g : B ⟶ C) :
    Ordinary.map (f ≫ g) = Ordinary.map f ≫ Ordinary.map g := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  exact LinearMap.ext (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_comp f g i)

def functor (R : Type u) [CommRing R] : CommAlgCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℕ where
  obj A := AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A
  map := Ordinary.map
  map_id := Ordinary.map_id
  map_comp := Ordinary.map_comp

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryDeRhamFunctor.Ordinary
