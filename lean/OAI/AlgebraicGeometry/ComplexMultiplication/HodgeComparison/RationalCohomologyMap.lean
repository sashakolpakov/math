import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation

/-! # Rational Cohomology Map -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCohomologyMap.CM.Construction

noncomputable section

/-! A cochain map from rational coefficients to a restricted complex
cochain complex induces the actual map on native complex cohomology. -/

open _root_.CategoryTheory

variable {K Q : CochainComplex (ModuleCat.{0} ℚ) ℕ}
  {L T : CochainComplex (ModuleCat.{0} ℂ) ℕ}

def rationalComplexCocycleMap (f : K ⟶ PositiveCohomologyConjugation.CM.Construction.restrictComplex L) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K n) : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles L n :=
  let d := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap f n c
  ⟨d.val, d.property⟩

def rationalComplexCohomologyMap (f : K ⟶ PositiveCohomologyConjugation.CM.Construction.restrictComplex L) (n : ℕ) :
    K.homology n ⟶ PositiveCohomologyConjugation.CM.Construction.restrictToRational.obj (L.homology n) :=
  HomologicalComplex.homologyMap f n ≫ ((L.sc n).mapHomologyIso PositiveCohomologyConjugation.CM.Construction.restrictToRational).hom

theorem rationalComplexCohomologyMap_class (f : K ⟶ PositiveCohomologyConjugation.CM.Construction.restrictComplex L) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K n) :
    rationalComplexCohomologyMap f n (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass K n c) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass L n (rationalComplexCocycleMap f n c) := by
  change ((L.sc n).mapHomologyIso PositiveCohomologyConjugation.CM.Construction.restrictToRational).hom
    (HomologicalComplex.homologyMap f n (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass K n c)) = _
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  exact PositiveCohomologyConjugation.CM.Construction.restrictHomology_class L n (rationalComplexCocycleMap f n c)

theorem rationalComplexCohomologyMap_naturality
    (f : K ⟶ PositiveCohomologyConjugation.CM.Construction.restrictComplex L) (g : Q ⟶ PositiveCohomologyConjugation.CM.Construction.restrictComplex T)
    (a : K ⟶ Q) (b : L ⟶ T)
    (h : a ≫ g = f ≫ (PositiveCohomologyConjugation.CM.Construction.restrictToRational.mapHomologicalComplex (ComplexShape.up ℕ)).map b)
    (n : ℕ) (x : K.homology n) :
    rationalComplexCohomologyMap g n (HomologicalComplex.homologyMap a n x) =
      HomologicalComplex.homologyMap b n (rationalComplexCohomologyMap f n x) := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective K n x
  have hc : rationalComplexCocycleMap g n (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap a n c) =
      AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap b n (rationalComplexCocycleMap f n c) := by
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (congrArg (fun k => k.f n) h) c.val
  have h₁ := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality a n c
  have h₂ := rationalComplexCohomologyMap_class g n (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap a n c)
  have h₃ := rationalComplexCohomologyMap_class f n c
  have h₄ := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality b n (rationalComplexCocycleMap f n c)
  exact (congrArg (rationalComplexCohomologyMap g n) h₁).trans
    (h₂.trans ((congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass T n) hc).trans
      (h₄.symm.trans (congrArg (HomologicalComplex.homologyMap b n) h₃).symm)))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCohomologyMap.CM.Construction
