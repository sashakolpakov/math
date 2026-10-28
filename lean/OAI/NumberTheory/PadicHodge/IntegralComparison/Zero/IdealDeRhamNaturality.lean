import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryDeRhamFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamComplexMap
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal

/-! # Ideal De Rham Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.IdealDeRhamNaturality

noncomputable section

/-!
# IntegralComparison: the ordinary-to-zero-ideal divided-power comparison is natural
-/

open _root_.CategoryTheory

universe u

variable {R : Type u} [CommRing R] {A B : CommAlgCat.{u} R}
  (f : A ⟶ B)
  (hf : DividedPowers.IsDPMorphism (dividedPowersBot A) (dividedPowersBot B) f.hom.toRingHom)

theorem forms_mk (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.formsEquiv R A n
      ((AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A ⊥ (dividedPowersBot A) n).mkQ ω) = ω :=
  Submodule.quotEquivOfEqBot_apply_mk _ _ _

theorem forms (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A ⊥ (dividedPowersBot A) n) :
    AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.formsEquiv R B n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap f hf n ω) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n (AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.formsEquiv R A n ω) := by
  obtain ⟨ω, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A ⊥ (dividedPowersBot A) n).mkQ_surjective ω
  rw [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_mk]
  exact (forms_mk R B n _).trans (congrArg (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n) (forms_mk R A n ω).symm)

theorem complexes : OrdinaryDeRhamFunctor.Ordinary.map f ≫ (AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.complexIso R B).hom =
    (AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.complexIso R A).hom ≫ PD.DeRhamComplexMap.map f hf := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  change (AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.formsEquiv R B n).symm (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n ω) =
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap f hf n ((AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.formsEquiv R A n).symm ω)
  apply (AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.formsEquiv R B n).injective
  exact ((AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.formsEquiv R B n).apply_symm_apply _).trans
    ((forms f hf n _).trans (congrArg (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n)
      ((AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.formsEquiv R A n).apply_symm_apply ω))).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.IdealDeRhamNaturality
