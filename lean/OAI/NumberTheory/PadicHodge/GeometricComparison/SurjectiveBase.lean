import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryBaseQuotient
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryDeRhamFunctor

/-! # Surjective Base -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SurjectiveBase.SurjectiveBaseDeRham

noncomputable section

/-! Surjective changes of the coefficient base identify the original ordinary
de Rham complexes, naturally in algebra maps. In particular this applies to
the canonical Witt-vector and p-adic-integer coefficient identification. -/

open _root_.CategoryTheory

universe u
variable (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
  (h : Function.Surjective (algebraMap R S))

def formsIso (n : ℕ) : ModuleCat.of R (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) ≅
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S A n)) := by
  let e := IntegralComparison.OrdinaryBaseQuotient.Ordinary.formsEquiv R S A h n
  refine (AddEquiv.toLinearEquiv (M := AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n)
    (M₂ := ↑((ModuleCat.restrictScalars (algebraMap R S)).obj
      (ModuleCat.of S (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S A n)))) e.toAddEquiv ?_).toModuleIso
  intro r ω
  change e (r • ω) = (algebraMap R S r) • e ω
  rw [← algebraMap_smul A r ω, e.map_smul,
    ← algebraMap_smul A (algebraMap R S r) (e ω), IsScalarTower.algebraMap_apply R S A]

def iso : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A ≅
    ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex (.up ℕ)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex S A) :=
  HomologicalComplex.Hom.isoOfComponents (formsIso R S A h) (by
    intro i j hij
    change i + 1 = j at hij
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    change (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex S A).d i (i + 1)
      (IntegralComparison.OrdinaryBaseQuotient.Ordinary.formsEquiv R S A h i ω) =
        IntegralComparison.OrdinaryBaseQuotient.Ordinary.formsEquiv R S A h (i + 1)
          ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A).d i (i + 1) ω)
    dsimp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    exact (IntegralComparison.OrdinaryBaseQuotient.Ordinary.differential R S A h i ω).symm)

variable (B : Type u) [CommRing B] [Algebra S B] [Algebra R B] [IsScalarTower R S B]
  (f : A →ₐ[S] B)

theorem forms_naturality (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    IntegralComparison.OrdinaryBaseQuotient.Ordinary.formsEquiv R S B h n
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (f.restrictScalars R)) n ω) =
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom f) n
      (IntegralComparison.OrdinaryBaseQuotient.Ordinary.formsEquiv R S A h n ω) := by
  obtain ⟨a, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n).mkQ_surjective ω
  induction a using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single v a =>
    change IntegralComparison.OrdinaryBaseQuotient.Ordinary.formsEquiv R S B h n
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (f.restrictScalars R)) n
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom f) n
        (IntegralComparison.OrdinaryBaseQuotient.Ordinary.formsEquiv R S A h n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v))
    rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol, IntegralComparison.OrdinaryBaseQuotient.Ordinary.formsEquiv_symbol,
      IntegralComparison.OrdinaryBaseQuotient.Ordinary.formsEquiv_symbol, AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol]
    rfl

theorem naturality : IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map (CommAlgCat.ofHom (f.restrictScalars R)) ≫
    (iso R S B h).hom = (iso R S A h).hom ≫
      ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex (.up ℕ)).map
        (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map (CommAlgCat.ofHom f)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact forms_naturality R S A h B f n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SurjectiveBase.SurjectiveBaseDeRham
