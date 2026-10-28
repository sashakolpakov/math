import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.Multiplication
import OAI.AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange

/-! # Betti End Additivity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiEndAdditivity.CM

noncomputable section

/-! Actual pullback on first Betti cohomology is additive in maps into a
projective abelian variety. The proof uses the proved H1 group-law formula
and then the canonical rational-to-complex coefficient extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.Multiplication

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) {X : Over Foundations.Scheme.ProjectiveSpace.complexBase}

def pairTop (f g : X ⟶ A.toOver) : Betti.Scheme.schemePointSpace X ⟶ AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointProductTop A :=
  TopCat.ofHom ⟨fun x => (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map g x),
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f).hom.continuous.prodMk
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map g).hom.continuous⟩

theorem pairTop_fst (f g : X ⟶ A.toOver) :
    pairTop A f g ≫ TopCat.prodFst = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f := rfl

theorem pairTop_snd (f g : X ⟶ A.toOver) :
    pairTop A f g ≫ TopCat.prodSnd = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map g := rfl

theorem pairTop_mul (f g : X ⟶ A.toOver) :
    pairTop A f g ≫ AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (f * g) := by
  apply TopCat.ext
  intro x
  change (x ≫ f) * (x ≫ g) = x ≫ (f * g)
  exact (MonObj.comp_mul x f g).symm

theorem rational_pullback_mul (f g : X ⟶ A.toOver)
    (c : A.variety.rationalCohomology 1) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 (f * g) c =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 f c +
        Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 g c := by
  have h := congrArg
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (pairTop A f g) 1)
    (AbelianModuli.ReferenceFamily.Product.Multiplication.abelianH1_multiplication A c)
  change AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (f * g)) 1 c =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) 1 c +
        AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map g) 1 c
  simpa only [map_add, AbelianModuli.ReferenceFamily.Product.Multiplication.productH1Left, AbelianModuli.ReferenceFamily.Product.Multiplication.productH1Right, AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.pullback_comp_apply,
    pairTop_mul, pairTop_fst, pairTop_snd] using h

theorem complex_pullback_mul (f g : X ⟶ A.toOver)
    (c : Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) A.toOver 1) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (f * g) c =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f c +
        Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 g c := by
  let : FiniteDimensional ℚ (A.variety.rationalCohomology 1) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite A.variety 1
  obtain ⟨z, rfl⟩ := ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_surjective
    (Betti.Scheme.schemePointSpace A.toOver) 1 c
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    abel
  | tmul r c =>
    let zc : Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) A.toOver 1 :=
      Betti.Scheme.schemeBettiRationalInclusion A.toOver 1 c
    change (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (f * g)).hom (r • zc) =
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f).hom (r • zc) +
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 g).hom (r • zc)
    simp only [map_smul]
    rw [← smul_add]
    apply congrArg (r • ·)
    have hn (u : X ⟶ A.toOver) :
        Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 u
          (Betti.Scheme.schemeBettiRationalInclusion A.toOver 1 c) =
        Betti.Scheme.schemeBettiRationalInclusion X 1 (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 u c) :=
      (ConcreteCategory.congr_hom (Betti.Scheme.schemeBettiRationalInclusion_naturality u 1) c).symm
    change Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (f * g)
      (Betti.Scheme.schemeBettiRationalInclusion A.toOver 1 c) = _
    rw [hn, hn, hn, rational_pullback_mul, map_add]
    rfl

theorem complex_pullback_mul_map (f g : X ⟶ A.toOver) :
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (f * g)).hom =
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f).hom +
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 g).hom :=
  LinearMap.ext (complex_pullback_mul A f g)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiEndAdditivity.CM
