import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseForms

/-! # Base Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseComplex

noncomputable section

/-! Canonical comparison of the actual ordinary and divided-power complexes for a principal base ideal. -/

open _root_.CategoryTheory

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (r : R) (δR : DividedPowers (Ideal.span {r}))
  (δA : DividedPowers (Ideal.span {algebraMap R A r}))
  (hδ : DividedPowers.IsDPMorphism δR δA (algebraMap R A))

def iso : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R A (Ideal.span {algebraMap R A r}) δA ≅ AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => ((BaseForms.formsEquiv R A r δR δA hδ n).restrictScalars R).toModuleIso)
    (by
      intro n m hnm
      change n + 1 = m at hnm
      subst m
      dsimp only [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro ω
      exact (BaseForms.differential R A r δR δA hδ n ω).symm)

def ofIdealEq (I : Ideal A) (δ : DividedPowers I) (hI : I = Ideal.span {algebraMap R A r})
    (hf : DividedPowers.IsDPMorphism δR δ (algebraMap R A)) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R A I δ ≅ AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A := by
  subst I
  exact iso R A r δR δ hf

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseComplex
