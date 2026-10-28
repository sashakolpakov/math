import OAI.AlgebraicGeometry.DivisorClass.Chern.SubspaceCechD
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMapComponents

/-! # Cech Sequence -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CechSequence

noncomputable section

section

/-!
# ChernClass: the relative kernel in the actual Cech total complex

The finite component decomposition lifts every total cochain whose subspace
restriction is zero. Its inclusion is injective and preserves the differential.
This supplies actual relative cocycles, rather than a new relative theory.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMapComponents.DoubleComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

variable {I : Type} (X : TopCat.{0}) (A : Set X) (U : I → Opens X)

theorem cechTotalInclusion_d_apply
    (K : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℚ) ℕ)
    (p q n : ℕ) (h : p + q = n) (c : Rational.Cech.RationalCech.CechCochain (K.X q) U p) :
    (Rational.Cech.RationalCech.cechTotalComplex U K).d n (n + 1) (Rational.Cech.RationalCech.cechTotalInclusion U K p q n h c) =
      Rational.Cech.RationalCech.cechTotalInclusion U K (p + 1) q (n + 1) (by omega) (Rational.Cech.RationalCech.cechDelta (K.X q) U p c) +
      ((-1 : ℤ) ^ p) • Rational.Cech.RationalCech.cechTotalInclusion U K p (q + 1) (n + 1) (by omega)
        (Rational.Cech.RationalCech.cechCoefficientMap U (K.d q (q + 1)) p c) :=
  ConcreteCategory.congr_hom (Rational.Cech.RationalCech.cechTotalInclusion_d U K p q n h) c

theorem cechTotalInclusion_map_apply
    {K N : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℚ) ℕ} (φ : K ⟶ N)
    (p q n : ℕ) (h : p + q = n) (c : Rational.Cech.RationalCech.CechCochain (K.X q) U p) :
    (Rational.Cech.RationalCech.cechTotalMap U φ).f n (Rational.Cech.RationalCech.cechTotalInclusion U K p q n h c) =
      Rational.Cech.RationalCech.cechTotalInclusion U N p q n h (Rational.Cech.RationalCech.cechCoefficientMap U (φ.f q) p c) :=
  ConcreteCategory.congr_hom (Rational.Cech.RationalCech.cechTotalInclusion_map U φ p q n h) c

abbrev relativeCechTotal := Rational.Cech.RationalCech.cechTotalComplex U (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativePresheafComplex (ModuleCat.of ℚ ℚ) X A)
abbrev ambientCechTotal := Rational.Cech.RationalCech.cechTotalComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)
abbrev subspaceCechTotal := Rational.Cech.RationalCech.cechTotalComplex U (SubspaceCechD.RationalCech.subspaceSingularPresheafComplex X A)

abbrev relativeCechTotalInclusion : relativeCechTotal X A U ⟶ ambientCechTotal X U :=
  Rational.Cech.RationalCech.cechTotalMap U (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativePresheafInclusion (ModuleCat.of ℚ ℚ) X A)

abbrev subspaceCechTotalRestriction : ambientCechTotal X U ⟶ subspaceCechTotal X A U :=
  Rational.Cech.RationalCech.cechTotalMap U (SubspaceCechD.RationalCech.subspacePresheafRestriction X A)

theorem relativeCechTotalInclusion_injective (n : ℕ) :
    Function.Injective ((relativeCechTotalInclusion X A U).f n) := by
  intro c d h
  apply AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.total_element_ext (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativePresheafComplex (ModuleCat.of ℚ ℚ) X A)) n
  intro p q hpq
  apply SubspaceCechD.RationalCech.relativeCechInclusion_injective X A U p q
  have he := congrArg (AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X))
    p q n hpq) h
  exact (AlgebraicTopology.DeRham.Comparison.DoubleComplexMapComponents.DoubleComplex.project_total_map (Rational.Cech.RationalCech.cechDoubleComplexMap U
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativePresheafInclusion (ModuleCat.of ℚ ℚ) X A)) p q n hpq c).symm.trans
      (he.trans (AlgebraicTopology.DeRham.Comparison.DoubleComplexMapComponents.DoubleComplex.project_total_map (Rational.Cech.RationalCech.cechDoubleComplexMap U
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativePresheafInclusion (ModuleCat.of ℚ ℚ) X A)) p q n hpq d))

/-- Each component of a total cochain with zero restriction has zero restriction. -/
theorem subspaceCechTotalRestriction_component (n p q : ℕ)
    (c : (ambientCechTotal X U).X n)
    (hc : (subspaceCechTotalRestriction X A U).f n c = 0) :
    SubspaceCechD.RationalCech.subspaceCechRestriction X A U p q
      (AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotalOrZero (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)) p q n c) = 0 := by
  have h := AlgebraicTopology.DeRham.Comparison.DoubleComplexMapComponents.DoubleComplex.projectOrZero_total_map (Rational.Cech.RationalCech.cechDoubleComplexMap U (SubspaceCechD.RationalCech.subspacePresheafRestriction X A)) p q n c
  change AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotalOrZero (Rational.Cech.RationalCech.cechDoubleComplex U (SubspaceCechD.RationalCech.subspaceSingularPresheafComplex X A)) p q n
      ((subspaceCechTotalRestriction X A U).f n c) = _ at h
  rw [hc, map_zero] at h
  exact h.symm

/-- Lift all homogeneous components and sum them in the existing finite totalization. -/
def relativeCechTotalLift (n : ℕ) (c : (ambientCechTotal X U).X n)
    (hc : (subspaceCechTotalRestriction X A U).f n c = 0) : (relativeCechTotal X A U).X n :=
  ∑ pq ∈ Finset.antidiagonal n,
    (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativePresheafComplex (ModuleCat.of ℚ ℚ) X A)).ιTotalOrZero
      (ComplexShape.up ℕ) pq.1 pq.2 n
      (SubspaceCechD.RationalCech.relativeCechLift X A U pq.1 pq.2
        (AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotalOrZero (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X))
          pq.1 pq.2 n c)
        (subspaceCechTotalRestriction_component X A U n pq.1 pq.2 c hc))

/-- The lift recovers exactly the original absolute total cochain. -/
theorem relativeCechTotalLift_inclusion (n : ℕ) (c : (ambientCechTotal X U).X n)
    (hc : (subspaceCechTotalRestriction X A U).f n c = 0) :
    (relativeCechTotalInclusion X A U).f n (relativeCechTotalLift X A U n c hc) = c := by
  unfold relativeCechTotalLift
  rw [map_sum]
  trans ∑ pq ∈ Finset.antidiagonal n,
    (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)).ιTotalOrZero
      (ComplexShape.up ℕ) pq.1 pq.2 n
      (AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotalOrZero (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)) pq.1 pq.2 n c)
  · apply Finset.sum_congr rfl
    intro pq hpq
    have h := AlgebraicTopology.DeRham.Comparison.DoubleComplexMapComponents.DoubleComplex.total_map_iotaOrZero (Rational.Cech.RationalCech.cechDoubleComplexMap U
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativePresheafInclusion (ModuleCat.of ℚ ℚ) X A)) pq.1 pq.2 n
      (SubspaceCechD.RationalCech.relativeCechLift X A U pq.1 pq.2
        (AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotalOrZero (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)) pq.1 pq.2 n c)
        (subspaceCechTotalRestriction_component X A U n pq.1 pq.2 c hc))
    change (relativeCechTotalInclusion X A U).f n _ =
      (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)).ιTotalOrZero
        (ComplexShape.up ℕ) pq.1 pq.2 n (SubspaceCechD.RationalCech.relativeCechInclusion X A U pq.1 pq.2 _) at h
    rw [SubspaceCechD.RationalCech.relativeCechLift_inclusion] at h
    exact h
  · exact AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.sum_iota_πTotalOrZero_apply
      (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)) n c

/-- A closed absolute cochain with zero restriction lifts to a closed relative cochain. -/
theorem relativeCechTotalLift_closed (n : ℕ) (c : (ambientCechTotal X U).X n)
    (hc : (subspaceCechTotalRestriction X A U).f n c = 0)
    (hd : (ambientCechTotal X U).d n (n + 1) c = 0) :
    (relativeCechTotal X A U).d n (n + 1) (relativeCechTotalLift X A U n c hc) = 0 := by
  apply relativeCechTotalInclusion_injective X A U (n + 1)
  have h := ConcreteCategory.congr_hom ((relativeCechTotalInclusion X A U).comm n (n + 1))
    (relativeCechTotalLift X A U n c hc)
  change (ambientCechTotal X U).d n (n + 1)
      ((relativeCechTotalInclusion X A U).f n (relativeCechTotalLift X A U n c hc)) =
    (relativeCechTotalInclusion X A U).f (n + 1)
      ((relativeCechTotal X A U).d n (n + 1) (relativeCechTotalLift X A U n c hc)) at h
  rw [relativeCechTotalLift_inclusion, hd] at h
  exact h.symm.trans (map_zero _).symm

end RationalCech

end

/-!
# ChernClass: the actual short exact sequence of relative Cech total complexes

Restriction is surjective by explicit extension of each finite homogeneous
component. The actual relative inclusion is injective and its image is
exactly the kernel already lifted in `RelativeCechTotal`.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMapComponents.DoubleComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

variable {I : Type} (X : TopCat.{0}) (A : Set X) (U : I → Opens X)

/-- Include a relative family and then restrict it: the result is zero. -/
theorem relativeCechInclusion_restrict (p q : ℕ)
    (c : Rational.Cech.RationalCech.CechCochain (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainDegreePresheaf (ModuleCat.of ℚ ℚ) X A q) U p) :
    SubspaceCechD.RationalCech.subspaceCechRestriction X A U p q (SubspaceCechD.RationalCech.relativeCechInclusion X A U p q c) = 0 := by
  funext a
  exact ConcreteCategory.congr_hom
    (congrArg (fun f => f.f q)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_restriction (ModuleCat.of ℚ ℚ)
        (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)))) (c a)

/-- The corresponding actual total cochain maps compose to zero. -/
theorem relativeCechTotalInclusion_restriction :
    relativeCechTotalInclusion X A U ≫ subspaceCechTotalRestriction X A U = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.total_element_ext (Rational.Cech.RationalCech.cechDoubleComplex U (SubspaceCechD.RationalCech.subspaceSingularPresheafComplex X A)) n
  intro p q hpq
  have h₁ := AlgebraicTopology.DeRham.Comparison.DoubleComplexMapComponents.DoubleComplex.project_total_map (Rational.Cech.RationalCech.cechDoubleComplexMap U (SubspaceCechD.RationalCech.subspacePresheafRestriction X A)) p q n hpq
    ((relativeCechTotalInclusion X A U).f n c)
  have h₂ := AlgebraicTopology.DeRham.Comparison.DoubleComplexMapComponents.DoubleComplex.project_total_map (Rational.Cech.RationalCech.cechDoubleComplexMap U
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativePresheafInclusion (ModuleCat.of ℚ ℚ) X A)) p q n hpq c
  change AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal (Rational.Cech.RationalCech.cechDoubleComplex U (SubspaceCechD.RationalCech.subspaceSingularPresheafComplex X A)) p q n hpq
      ((subspaceCechTotalRestriction X A U).f n ((relativeCechTotalInclusion X A U).f n c)) =
    SubspaceCechD.RationalCech.subspaceCechRestriction X A U p q
      (AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)) p q n hpq
        ((relativeCechTotalInclusion X A U).f n c)) at h₁
  change AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)) p q n hpq
      ((relativeCechTotalInclusion X A U).f n c) = SubspaceCechD.RationalCech.relativeCechInclusion X A U p q _ at h₂
  rw [h₂, relativeCechInclusion_restrict] at h₁
  exact h₁.trans (map_zero _).symm

/-- Extend each homogeneous component to its actual ambient cochain domain. -/
def subspaceCechTotalExtension (n : ℕ) (c : (subspaceCechTotal X A U).X n) :
    (ambientCechTotal X U).X n :=
  ∑ pq ∈ Finset.antidiagonal n,
    (Rational.Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)).ιTotalOrZero
      (ComplexShape.up ℕ) pq.1 pq.2 n
      (SubspaceCechD.RationalCech.subspaceCechExtension X A U pq.1 pq.2
        (AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotalOrZero (Rational.Cech.RationalCech.cechDoubleComplex U (SubspaceCechD.RationalCech.subspaceSingularPresheafComplex X A)) pq.1 pq.2 n c))

/-- The extension restricts back to the given total cochain. -/
theorem subspaceCechTotalExtension_restrict (n : ℕ) (c : (subspaceCechTotal X A U).X n) :
    (subspaceCechTotalRestriction X A U).f n (subspaceCechTotalExtension X A U n c) = c := by
  unfold subspaceCechTotalExtension
  rw [map_sum]
  trans ∑ pq ∈ Finset.antidiagonal n,
    (Rational.Cech.RationalCech.cechDoubleComplex U (SubspaceCechD.RationalCech.subspaceSingularPresheafComplex X A)).ιTotalOrZero
      (ComplexShape.up ℕ) pq.1 pq.2 n
      (AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotalOrZero (Rational.Cech.RationalCech.cechDoubleComplex U (SubspaceCechD.RationalCech.subspaceSingularPresheafComplex X A)) pq.1 pq.2 n c)
  · apply Finset.sum_congr rfl
    intro pq hpq
    have h := AlgebraicTopology.DeRham.Comparison.DoubleComplexMapComponents.DoubleComplex.total_map_iotaOrZero (Rational.Cech.RationalCech.cechDoubleComplexMap U (SubspaceCechD.RationalCech.subspacePresheafRestriction X A))
      pq.1 pq.2 n (SubspaceCechD.RationalCech.subspaceCechExtension X A U pq.1 pq.2
        (AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotalOrZero (Rational.Cech.RationalCech.cechDoubleComplex U (SubspaceCechD.RationalCech.subspaceSingularPresheafComplex X A)) pq.1 pq.2 n c))
    change (subspaceCechTotalRestriction X A U).f n _ =
      (Rational.Cech.RationalCech.cechDoubleComplex U (SubspaceCechD.RationalCech.subspaceSingularPresheafComplex X A)).ιTotalOrZero
        (ComplexShape.up ℕ) pq.1 pq.2 n (SubspaceCechD.RationalCech.subspaceCechRestriction X A U pq.1 pq.2 _) at h
    rw [SubspaceCechD.RationalCech.subspaceCechExtension_restrict] at h
    exact h
  · exact AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.sum_iota_πTotalOrZero_apply (Rational.Cech.RationalCech.cechDoubleComplex U (SubspaceCechD.RationalCech.subspaceSingularPresheafComplex X A)) n c

/-- The short complex is built from the existing relative inclusion and subspace restriction. -/
def relativeCechSequence : ShortComplex (CochainComplex (ModuleCat.{0} ℚ) ℕ) :=
  ShortComplex.mk (relativeCechTotalInclusion X A U) (subspaceCechTotalRestriction X A U)
    (relativeCechTotalInclusion_restriction X A U)

/-- Exactness, injectivity, and surjectivity hold in every actual total degree. -/
theorem relativeCechSequence_shortExact : (relativeCechSequence X A U).ShortExact := by
  apply (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mpr
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro c hc
    exact ⟨relativeCechTotalLift X A U n c hc, relativeCechTotalLift_inclusion X A U n c hc⟩
  · exact (ModuleCat.mono_iff_injective _).mpr (relativeCechTotalInclusion_injective X A U n)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro c
    exact ⟨subspaceCechTotalExtension X A U n c, subspaceCechTotalExtension_restrict X A U n c⟩

end RationalCech

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CechSequence
