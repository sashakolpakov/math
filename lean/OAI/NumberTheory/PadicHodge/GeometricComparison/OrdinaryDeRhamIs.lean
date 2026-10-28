import OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientQuotientOf
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryDeRhamFunctor

/-! # Ordinary De Rham Is -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryDeRhamIs.OrdinaryDeRhamCoefficientReduction

noncomputable section

/-! Algebra maps whose targets kill a coefficient ideal induce
canonical natural maps from the quotient ordinary de Rham complexes. -/

open _root_.CategoryTheory

universe u
variable (R : Type u) [CommRing R] (I : Ideal R)
  {A B : CommAlgCat.{u} R} (α : A ⟶ B)
  (hB : ∀ r, r ∈ I → algebraMap R B r = 0)

include hB in
theorem kernel (n : ℕ) :
    (I • ⊤ : Submodule R (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n)) ≤
      LinearMap.ker ((IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map α).f n).hom := by
  apply CoefficientQuotientOf.CoefficientQuotientLift.kernel_of_annihilation R I (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map α)
  intro m r hr ω
  let ω' : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B m := ω
  exact (algebraMap_smul B r ω').symm.trans
    ((congrArg (fun b : B => b • ω') (hB r hr)).trans (zero_smul B ω'))

def map : IntegralComparison.Module.IdealQuotient.complex R I (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A) ⟶
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R B :=
  CoefficientQuotientOf.CoefficientQuotientLift.map R I (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map α) (kernel R I α hB)

theorem factorization : IntegralComparison.Module.IdealQuotient.complexProjection R I (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A) ≫
    OrdinaryDeRhamCoefficientReduction.map R I α hB = IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map α :=
  CoefficientQuotientOf.CoefficientQuotientLift.factorization R I (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map α) (kernel R I α hB)

theorem isIso_of_comparison
    (e : IntegralComparison.Module.IdealQuotient.complex R I (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A) ≅ AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R B)
    (he : IntegralComparison.Module.IdealQuotient.complexProjection R I (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A) ≫ e.hom =
      IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map α) : IsIso (OrdinaryDeRhamCoefficientReduction.map R I α hB) := by
  unfold OrdinaryDeRhamCoefficientReduction.map
  exact (CoefficientQuotientOf.CoefficientQuotientLift.unique R I (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map α) (kernel R I α hB) e.hom he).symm ▸
    (inferInstanceAs (IsIso e.hom))

variable {A' B' : CommAlgCat.{u} R} (β : A' ⟶ B')
  (hB' : ∀ r, r ∈ I → algebraMap R B' r = 0)
  (f : A ⟶ A') (g : B ⟶ B') (hsquare : α ≫ g = f ≫ β)

include hsquare in
theorem naturality : OrdinaryDeRhamCoefficientReduction.map R I α hB ≫ IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map g =
    (((IntegralComparison.Module.IdealQuotient.functor R I).mapHomologicalComplex (.up ℕ)).map
      (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map f)) ≫ OrdinaryDeRhamCoefficientReduction.map R I β hB' :=
  CoefficientQuotientOf.CoefficientQuotientLift.naturality R I (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map α) (kernel R I α hB)
    (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map β) (kernel R I β hB')
    (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map f) (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map g)
    ((IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map_comp α g).symm.trans
      ((congrArg IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map hsquare).trans (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map_comp f β)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryDeRhamIs.OrdinaryDeRhamCoefficientReduction
