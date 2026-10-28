import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.AbsoluteCycleClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.GlobalSpecialization

/-! # Graded Absolute Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GradedAbsoluteClass.BundleCycles

noncomputable section

section

/-! The canonical geometric class extends linearly to every finite
dimension-graded cycle on a smooth integral complex scheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]

theorem schemeCycleClass_congrSupport (C D : IrreducibleCloseds X.left) (h : C = D) (p : ℕ)
    (hc : Foundations.Scheme.SupportDimension.supportTranscendenceDimension C X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension D X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    AbsoluteCycleClass.BundleCycles.schemeCycleClass X C p hc = AbsoluteCycleClass.BundleCycles.schemeCycleClass X D p hd := by
  subst D
  rfl

def schemeGradedCycleClass (d p : ℕ) (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) →ₗ[ℚ] (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X (p + p)) :=
  Finsupp.linearCombination ℚ (fun x => AbsoluteCycleClass.BundleCycles.schemeCycleClass X (irreducibleSetEquivPoints.symm x.val) p
    ((congrArg (fun n => n + p) x.property).trans hd))

theorem schemeGradedCycleClass_single (d p : ℕ) (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d) (a : ℚ) :
    schemeGradedCycleClass X d p hd (Finsupp.single x a) =
      a • AbsoluteCycleClass.BundleCycles.schemeCycleClass X (irreducibleSetEquivPoints.symm x.val) p
        ((congrArg (fun n => n + p) x.property).trans hd) := Finsupp.linearCombination_single ℚ a x

end

/-! The ordinary class of a finite graded cycle in degree twice its
codimension, with the explicit equivalence to the sum-degree convention. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

def schemeBettiDegreeEquiv (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {m n : ℕ} (h : m = n) :
    (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X m) ≃ₗ[ℚ] (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X n) := by
  subst n
  exact LinearEquiv.refl ℚ _

theorem schemeBettiDegreeEquiv_apply (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {m n : ℕ} (h : m = n)
    (a : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X m) :
    schemeBettiDegreeEquiv X h a = cast (congrArg (fun k => (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X k : Type)) h) a := by
  subst n
  rfl

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]

def schemeGradedAbsoluteCycleClass (d p : ℕ) (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) →ₗ[ℚ] (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X (2 * p)) :=
  Finsupp.linearCombination ℚ (fun x => AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X (irreducibleSetEquivPoints.symm x.val) p
    ((congrArg (fun n => n + p) x.property).trans hd))

theorem schemeGradedAbsoluteCycleClass_single (d p : ℕ) (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d) (a : ℚ) :
    schemeGradedAbsoluteCycleClass X d p hd (Finsupp.single x a) =
      a • AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X (irreducibleSetEquivPoints.symm x.val) p
        ((congrArg (fun n => n + p) x.property).trans hd) := Finsupp.linearCombination_single ℚ a x

theorem schemeGradedCycleClass_eq_degreeEquiv (d p : ℕ) (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    schemeGradedCycleClass X d p hd =
      (schemeBettiDegreeEquiv X (two_mul p)).toLinearMap.comp (schemeGradedAbsoluteCycleClass X d p hd) := by
  apply Finsupp.lhom_ext
  intro x a
  change schemeGradedCycleClass X d p hd (Finsupp.single x a) =
    schemeBettiDegreeEquiv X (two_mul p) (schemeGradedAbsoluteCycleClass X d p hd (Finsupp.single x a))
  rw [schemeGradedCycleClass_single, schemeGradedAbsoluteCycleClass_single, map_smul,
    schemeBettiDegreeEquiv_apply]
  rfl

theorem schemeGradedAbsoluteCycleClass_zero_iff (d p : ℕ) (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (a : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) :
    schemeGradedAbsoluteCycleClass X d p hd a = 0 ↔ schemeGradedCycleClass X d p hd a = 0 := by
  rw [schemeGradedCycleClass_eq_degreeEquiv, LinearMap.comp_apply]
  exact (map_eq_zero_iff _ (schemeBettiDegreeEquiv X (two_mul p)).injective).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GradedAbsoluteClass.BundleCycles
