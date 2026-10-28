import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveChartCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter
import OAI.AlgebraicGeometry.DivisorClass.Chern.AnalyticTransitions
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme

/-! # Projective Chart Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveChartPoints

noncomputable section

/-! Actual projective-chart maps evaluate to their normalized complex
coordinates on the original scheme-point space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme
open OAI.AlgebraicGeometry.DivisorClass.Chern.AnalyticTransitions.Construction (globalSectionEvaluation)
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

theorem globalSectionEvaluation_base (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation p).comp
      (X.hom.appTop.hom.comp Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.complexSectionRingEquiv.symm.toRingHom) = RingHom.id ℂ := by
  apply RingHom.ext
  intro z
  have h := congrArg (fun a : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Foundations.Scheme.ProjectiveSpace.complexBase => a.appTop) p.w
  have hz := ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso (.of ℂ)).inv z)
  change p.left.appTop (X.hom.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv z)) =
    (Scheme.ΓSpecIso (.of ℂ)).inv z at hz
  change (Scheme.ΓSpecIso (.of ℂ)).hom
    (p.left.appTop (X.hom.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv z))) = z
  rw [hz]
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of ℂ)).inv_hom_id z

theorem complexPoint_toSpec (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    p.left ≫ X.left.toSpecΓ = Spec.map (CommRingCat.ofHom (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation p)) :=
  (Scheme.toSpecΓ_naturality p.left).trans
    ((congrArg (fun a => a ≫ Spec.map p.left.appTop)
      (SpecMap_ΓSpecIso_hom (.of ℂ)).symm).trans (Spec.map_comp _ _).symm)

theorem projectiveChartEvaluation_native {n : ℕ} (v : Fin (n + 1) → ℂ)
    (i : Fin (n + 1)) (hi : v i = 1) :
    HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation (RingHom.id ℂ) v i hi =
      (MvPolynomial.eval (fun j : {j : Fin (n + 1) // j ≠ i} => v j.val)).comp
        (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial n i) := by
  have hv : Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i (fun j : {j : Fin (n + 1) // j ≠ i} => v j.val) = v := by
    funext j
    by_cases hji : j = i
    · subst j
      exact (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne_self i _).trans hi.symm
    · exact Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne_of_ne i j _ hji
  apply RingHom.ext
  intro z
  obtain ⟨d, q, hq, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading ℂ n) (MvPolynomial.isHomogeneous_X ℂ i) z
  have hq' : q ∈ HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading ℂ n d := by
    simpa only [smul_eq_mul, mul_one] using hq
  change HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation (RingHom.id ℂ) v i hi _ =
    MvPolynomial.eval _ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial n i _)
  rw [HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation_mk (RingHom.id ℂ) v i hi d q hq',
    Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial_mk n i d q hq, Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.eval_dehomogenize, hv]
  rfl

theorem projectiveChartMap_point {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    {n : ℕ} (v : Fin (n + 1) → Γ(X.left, ⊤)) (i : Fin (n + 1)) (hi : v i = 1) :
    p.left ≫ HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartMap (X.hom.appTop.hom.comp Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.complexSectionRingEquiv.symm.toRingHom)
      v i hi =
      Spec.map (CommRingCat.ofHom (MvPolynomial.eval
        (fun j : {j : Fin (n + 1) // j ≠ i} => DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation p (v j.val)))) ≫
        Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i := by
  let c := X.hom.appTop.hom.comp Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.complexSectionRingEquiv.symm.toRingHom
  let w (j : Fin (n + 1)) := DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation p (v j)
  have hw : w i = 1 := (congrArg (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation p) hi).trans (map_one _)
  have he : (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation p).comp (HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation c v i hi) =
      HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation (RingHom.id ℂ) w i hw := by
    have h := HilbertConstruction.ProjectiveChart.Naturality.projectiveChartEvaluation_comp (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation p) c v i hi
    have hb : (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation p).comp c = RingHom.id ℂ := globalSectionEvaluation_base X p
    rw [hb] at h
    exact h
  have hring : CommRingCat.ofHom (HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation c v i hi) ≫
      CommRingCat.ofHom (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation p) =
      CommRingCat.ofHom ((MvPolynomial.eval
        (fun j : {j : Fin (n + 1) // j ≠ i} => w j.val)).comp
          (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial n i)) :=
    congrArg CommRingCat.ofHom (he.trans (projectiveChartEvaluation_native w i hw))
  let a := Spec.map (CommRingCat.ofHom (HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation c v i hi))
  let b := Proj.awayι (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading ℂ n) (MvPolynomial.X i)
    (show MvPolynomial.X i ∈ HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading ℂ n 1 from MvPolynomial.isHomogeneous_X ℂ i)
    Nat.zero_lt_one
  calc
    _ = (p.left ≫ X.left.toSpecΓ) ≫ a ≫ b := (Category.assoc _ _ _).symm
    _ = Spec.map (CommRingCat.ofHom (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation p)) ≫ a ≫ b :=
      congrArg (fun z => z ≫ a ≫ b) (complexPoint_toSpec X p)
    _ = Spec.map (CommRingCat.ofHom (HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation c v i hi) ≫
        CommRingCat.ofHom (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation p)) ≫ b :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ b) (Spec.map_comp _ _).symm)
    _ = _ := by
      rw [hring]
      change Spec.map (CommRingCat.ofHom (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial n i) ≫
        CommRingCat.ofHom (MvPolynomial.eval
          (fun j : {j : Fin (n + 1) // j ≠ i} => w j.val))) ≫ b = _
      rw [Spec.map_comp, Category.assoc]
      exact congrArg (fun z => Spec.map (CommRingCat.ofHom (MvPolynomial.eval
        (fun j : {j : Fin (n + 1) // j ≠ i} => w j.val))) ≫ z)
          (Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec_inv_ι n i).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveChartPoints
