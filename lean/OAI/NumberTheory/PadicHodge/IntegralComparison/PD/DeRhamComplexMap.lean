import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal

/-! # De Rham Complex Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamComplexMap

noncomputable section

/-!
# IntegralComparison: canonical maps of the original divided-power de Rham complexes
-/

open _root_.CategoryTheory

universe u

variable {R : Type u} [CommRing R] {A B C : CommAlgCat.{u} R}
  {I : Ideal A} {J : Ideal B} {L : Ideal C}
  {δI : DividedPowers I} {δJ : DividedPowers J} {δL : DividedPowers L}

def map (f : A ⟶ B) (hf : DividedPowers.IsDPMorphism δI δJ f.hom.toRingHom) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R A I δI ⟶ AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R B J δJ where
  f i := ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap f hf i)
  comm' i j hij := by
    change i + 1 = j at hij
    subst j
    dsimp only [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    exact LinearMap.ext (fun ω => (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_differential f hf i ω).symm)

theorem map_id (hf : DividedPowers.IsDPMorphism δI δI (𝟙 A : A ⟶ A).hom.toRingHom) :
    map (𝟙 A) hf = 𝟙 (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R A I δI) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  exact LinearMap.ext (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_id hf i)

theorem map_comp (f : A ⟶ B) (g : B ⟶ C)
    (hf : DividedPowers.IsDPMorphism δI δJ f.hom.toRingHom)
    (hg : DividedPowers.IsDPMorphism δJ δL g.hom.toRingHom)
    (hfg : DividedPowers.IsDPMorphism δI δL (f ≫ g).hom.toRingHom) :
    map (f ≫ g) hfg = map f hf ≫ map g hg := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  exact LinearMap.ext (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_comp f g hf hg hfg i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamComplexMap
