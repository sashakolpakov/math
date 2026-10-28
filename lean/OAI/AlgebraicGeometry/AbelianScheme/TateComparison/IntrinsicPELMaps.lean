import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriodNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter

/-! # Intrinsic PEL Maps -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicPELMaps

noncomputable section

section

/-! The period–Tate comparison intertwines the actual integral PEL
action on a projective complex abelian scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction

variable {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom) (q : ℕ) [Fact q.Prime]

def nativeToSchemeRationalTateEquiv :
    Rational.rationalTateModule (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).toOver (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q ≃ₗ[ℚ_[q]]
      Rational.rationalTateModule A.scheme (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q :=
  LinearEquiv.baseChange ℤ_[q] ℚ_[q] _ _ (TateProducts.Tate.mapEquiv q (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativePointEquiv A P).toAdditive)

theorem nativeToSchemeRationalTateEquiv_map :
    (nativeToSchemeRationalTateEquiv A P q).toLinearMap =
      Rational.rationalTateMap (T := Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A P).hom := by
  rfl

def pelRationalPeriodTateEquiv :
    ℚ_[q] ⊗[ℚ] AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) ≃ₗ[ℚ_[q]]
      Rational.rationalTateModule A.scheme (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q :=
  (RationalPeriod.rationalPeriodTateEquiv (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) q).trans (nativeToSchemeRationalTateEquiv A P q)

theorem rationalTateMap_congr {S : Scheme.{0}} {X Y : Over S}
    [GrpObj X] [IsCommMonObj X] [GrpObj Y] [IsCommMonObj Y] (T : Over S)
    (f f' : X ⟶ Y) [IsMonHom f] [IsMonHom f'] (heq : f = f') :
    Rational.rationalTateMap (T := T) (q := q) f = Rational.rationalTateMap (T := T) (q := q) f' := by
  cases heq
  rfl

variable {E : Type} [Field E]
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

theorem nativeRationalAction_eq (a : NumberField.RingOfIntegers E) :
    AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap A P ρ a) = AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction A P ρ a := rfl

theorem nativeToSchemeRationalTate_intertwines (a : NumberField.RingOfIntegers E) :
    (Rational.rationalTateMap (T := Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) (ρ.map a)).comp
        (nativeToSchemeRationalTateEquiv A P q).toLinearMap =
      (nativeToSchemeRationalTateEquiv A P q).toLinearMap.comp
        (Rational.rationalTateMap (T := Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) (AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap A P ρ a)) := by
  rw [nativeToSchemeRationalTateEquiv_map, ← Functor.rationalTateMap_comp, ← Functor.rationalTateMap_comp]
  apply rationalTateMap_congr
  simp only [AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem pelRationalPeriodTate_intertwines (a : NumberField.RingOfIntegers E) :
    (Rational.rationalTateMap (T := Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) (ρ.map a)).comp
        (pelRationalPeriodTateEquiv A P q).toLinearMap =
      (pelRationalPeriodTateEquiv A P q).toLinearMap.comp
        ((AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction A P ρ a).baseChange ℚ_[q]) := by
  change (Rational.rationalTateMap (T := Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) (ρ.map a)).comp
    ((nativeToSchemeRationalTateEquiv A P q).toLinearMap.comp (RationalPeriod.rationalPeriodTateEquiv (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) q).toLinearMap) =
      ((nativeToSchemeRationalTateEquiv A P q).toLinearMap.comp (RationalPeriod.rationalPeriodTateEquiv (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) q).toLinearMap).comp _
  rw [← LinearMap.comp_assoc, nativeToSchemeRationalTate_intertwines, LinearMap.comp_assoc,
    RationalPeriodNaturality.rationalPeriodTate_natural, nativeRationalAction_eq, LinearMap.comp_assoc]

theorem pelRationalPeriodTate_intertwines_apply (a : NumberField.RingOfIntegers E)
    (z : ℚ_[q] ⊗[ℚ] AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) :
    Rational.rationalTateMap (T := Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) (ρ.map a)
        (pelRationalPeriodTateEquiv A P q z) =
      pelRationalPeriodTateEquiv A P q (((AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction A P ρ a).baseChange ℚ_[q]) z) :=
  LinearMap.congr_fun (pelRationalPeriodTate_intertwines A P q ρ a) z

end

/-! Naturality of the actual period–Tate comparison for maps between
two projective complex abelian schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter

variable {g h : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
  (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h Foundations.Scheme.ProjectiveSpace.complexBase)
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
  (Q : Foundations.Scheme.SmoothProjective.ProjectivePresentation B.scheme.left B.scheme.hom)

def nativePELHom (f : A.scheme ⟶ B.scheme) : (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).toOver ⟶ (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B Q).toOver :=
  (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A P).hom ≫ f ≫ (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B Q).inv

instance (f : A.scheme ⟶ B.scheme) [IsMonHom f] : IsMonHom (nativePELHom A B P Q f) := by
  unfold nativePELHom
  infer_instance

theorem nativePELHom_pointMap (f : A.scheme ⟶ B.scheme) :
    TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous (nativePELHom A B P Q f)) =
      TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f) := by
  apply TopCat.ext
  intro p
  apply Over.OverMorphism.ext
  change p.left ≫ (𝟙 _ ≫ f.left ≫ 𝟙 _) = p.left ≫ f.left
  simp only [Category.id_comp]
  exact congrArg (fun a => p.left ≫ a) (Category.comp_id f.left)

variable (q : ℕ) [Fact q.Prime] (f : A.scheme ⟶ B.scheme) [IsMonHom f]

theorem nativeToSchemeRationalTate_natural :
    (Rational.rationalTateMap (T := Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) f).comp
        (nativeToSchemeRationalTateEquiv A P q).toLinearMap =
      (nativeToSchemeRationalTateEquiv B Q q).toLinearMap.comp
        (Rational.rationalTateMap (T := Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) (nativePELHom A B P Q f)) := by
  rw [nativeToSchemeRationalTateEquiv_map, nativeToSchemeRationalTateEquiv_map,
    ← Functor.rationalTateMap_comp, ← Functor.rationalTateMap_comp]
  apply rationalTateMap_congr
  simp only [nativePELHom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem pelRationalPeriodTate_natural :
    (Rational.rationalTateMap (T := Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) f).comp
        (pelRationalPeriodTateEquiv A P q).toLinearMap =
      (pelRationalPeriodTateEquiv B Q q).toLinearMap.comp
        ((AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (nativePELHom A B P Q f)).baseChange ℚ_[q]) := by
  change (Rational.rationalTateMap (T := Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) f).comp
    ((nativeToSchemeRationalTateEquiv A P q).toLinearMap.comp
      (RationalPeriod.rationalPeriodTateEquiv (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) q).toLinearMap) =
    ((nativeToSchemeRationalTateEquiv B Q q).toLinearMap.comp
      (RationalPeriod.rationalPeriodTateEquiv (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B Q) q).toLinearMap).comp _
  rw [← LinearMap.comp_assoc, nativeToSchemeRationalTate_natural, LinearMap.comp_assoc,
    RationalPeriodNaturality.rationalPeriodTate_natural, LinearMap.comp_assoc]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicPELMaps
