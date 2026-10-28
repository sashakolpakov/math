import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseFormCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamComplexMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryDeRhamFunctor

/-! # Base Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseNaturality

noncomputable section

/-! The actual principal-base PD-to-ordinary de Rham comparison is natural for divided-power morphisms. -/

open _root_.CategoryTheory

universe u

theorem forms_mk (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (r : R) (δR : DividedPowers (Ideal.span {r})) (I : Ideal A) (δ : DividedPowers I)
    (hI : I = Ideal.span {algebraMap R A r}) (hδ : DividedPowers.IsDPMorphism δR δ (algebraMap R A))
    (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    BaseFormCoordinates.formsEquiv R A r δR I δ hI hδ n
      ((AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ n).mkQ ω) = ω := by
  subst I
  exact Submodule.quotEquivOfEqBot_apply_mk _ (BaseForms.relations_eq_bot R A r δR δ hδ n) ω

theorem component (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (r : R) (δR : DividedPowers (Ideal.span {r})) (I : Ideal A) (δ : DividedPowers I)
    (hI : I = Ideal.span {algebraMap R A r}) (hδ : DividedPowers.IsDPMorphism δR δ (algebraMap R A))
    (n : ℕ) : (BaseComplex.ofIdealEq R A r δR I δ hI hδ).hom.f n =
      ModuleCat.ofHom ((BaseFormCoordinates.formsEquiv R A r δR I δ hI hδ n).toLinearMap.restrictScalars R) := by
  subst I
  rfl

variable {R : Type u} [CommRing R] (r : R) (δR : DividedPowers (Ideal.span {r}))
  {A B : CommAlgCat.{u} R} {I : Ideal A} {J : Ideal B}
  {δI : DividedPowers I} {δJ : DividedPowers J}
  (hI : I = Ideal.span {algebraMap R A r}) (hJ : J = Ideal.span {algebraMap R B r})
  (hA : DividedPowers.IsDPMorphism δR δI (algebraMap R A))
  (hB : DividedPowers.IsDPMorphism δR δJ (algebraMap R B))
  (f : A ⟶ B) (hf : DividedPowers.IsDPMorphism δI δJ f.hom.toRingHom)

theorem forms (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δI n) :
    BaseFormCoordinates.formsEquiv R B r δR J δJ hJ hB n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap f hf n ω) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n (BaseFormCoordinates.formsEquiv R A r δR I δI hI hA n ω) := by
  obtain ⟨ω, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δI n).mkQ_surjective ω
  rw [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_mk]
  exact (forms_mk R B r δR J δJ hJ hB n _).trans
    (congrArg (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n) (forms_mk R A r δR I δI hI hA n ω).symm)

theorem complexes : PD.DeRhamComplexMap.map f hf ≫ (BaseComplex.ofIdealEq R B r δR J δJ hJ hB).hom =
    (BaseComplex.ofIdealEq R A r δR I δI hI hA).hom ≫ OrdinaryDeRhamFunctor.Ordinary.map f := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (PD.DeRhamComplexMap.map f hf).f n ≫ (BaseComplex.ofIdealEq R B r δR J δJ hJ hB).hom.f n =
    (BaseComplex.ofIdealEq R A r δR I δI hI hA).hom.f n ≫ (OrdinaryDeRhamFunctor.Ordinary.map f).f n
  rw [component, component]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact forms r δR hI hJ hA hB f hf n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseNaturality
