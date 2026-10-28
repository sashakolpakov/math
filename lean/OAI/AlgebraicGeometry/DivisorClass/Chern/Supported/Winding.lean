import OAI.AlgebraicGeometry.DivisorClass.Chern.WindingCech
import OAI.AlgebraicGeometry.DivisorClass.Chern.WindingComparisonD
import OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport

/-! # Winding -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.Winding

noncomputable section

/-!
# ChernClass: supported winding and invariance under extending units

The actual connecting map of a pair turns winding on the complement into a
relative degree-two class. Multiplication by any nonvanishing function on the
whole ambient space leaves this relative class unchanged, by exactness and
proved singular naturality. Integer powers have their actual multiplicity.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : TopCat.{0})

/-- The product law transfers through the proved Cech-to-singular comparison. -/
theorem singularWindingClass_mul (f g : C(X, ℂ))
    (hf : ∀ x, f x ≠ 0) (hg : ∀ x, g x ≠ 0) :
    WindingSingular.singularWindingClass X (f * g) (fun x => mul_ne_zero (hf x) (hg x)) =
      WindingSingular.singularWindingClass X f hf + WindingSingular.singularWindingClass X g hg := by
  apply neg_injective
  have h := WindingCech.RationalCech.logarithmicWindingClass_mul X f g hf hg
  simpa only [WindingComparisonD.RationalCech.logarithmicWindingClass_eq_neg_singularWindingClass, neg_add] using h

theorem singularWindingClass_int_power (g f : C(X, ℂ))
    (hg : ∀ x, g x ≠ 0) (hf : ∀ x, f x ≠ 0) (m : ℤ)
    (hfg : ∀ x, f x = g x ^ m) :
    WindingSingular.singularWindingClass X f hf = m • WindingSingular.singularWindingClass X g hg := by
  apply neg_injective
  have h := WindingCech.RationalCech.logarithmicWindingClass_int_power X g f hg hf m hfg
  simpa only [WindingComparisonD.RationalCech.logarithmicWindingClass_eq_neg_singularWindingClass, smul_neg] using h

variable (A : Set X)

/-- The genuine degree-two connecting class of the complement's winding. -/
def supportedWindingClass (g : C(A, ℂ)) (hg : ∀ x, g x ≠ 0) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting (ModuleCat.of ℚ ℚ) X A 1 (WindingSingular.singularWindingClass (TopCat.of A) g hg)

theorem supportedWindingClass_congr (g f : C(A, ℂ))
    (hg : ∀ x, g x ≠ 0) (hf : ∀ x, f x ≠ 0) (h : g = f) :
    supportedWindingClass X A g hg = supportedWindingClass X A f hf := by
  subst f
  rfl

/-- The logarithmic Cech construction gives the same relative class, with
its now-proved minus sign. -/
theorem supportedWindingClass_logarithmic (g : C(A, ℂ)) (hg : ∀ x, g x ≠ 0) :
    supportedWindingClass X A g hg =
      -AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting (ModuleCat.of ℚ ℚ) X A 1
        (WindingCech.RationalCech.logarithmicWindingClass (TopCat.of A) g hg) := by
  rw [WindingComparisonD.RationalCech.logarithmicWindingClass_eq_neg_singularWindingClass, map_neg, neg_neg]
  rfl

theorem supportedWindingClass_mul (f g : C(A, ℂ))
    (hf : ∀ x, f x ≠ 0) (hg : ∀ x, g x ≠ 0) :
    supportedWindingClass X A (f * g) (fun x => mul_ne_zero (hf x) (hg x)) =
      supportedWindingClass X A f hf + supportedWindingClass X A g hg := by
  unfold supportedWindingClass
  rw [singularWindingClass_mul, map_add]

theorem supportedWindingClass_int_power (g f : C(A, ℂ))
    (hg : ∀ x, g x ≠ 0) (hf : ∀ x, f x ≠ 0) (m : ℤ)
    (hfg : ∀ x, f x = g x ^ m) :
    supportedWindingClass X A f hf = m • supportedWindingClass X A g hg := by
  unfold supportedWindingClass
  rw [singularWindingClass_int_power (TopCat.of A) g f hg hf m hfg, map_zsmul]

/-- A nonvanishing function which extends across the support contributes
zero, even when it has no global continuous logarithm. -/
theorem supportedWindingClass_extending_unit (u : C(X, ℂ)) (hu : ∀ x, u x ≠ 0) :
    supportedWindingClass X A (u.comp ⟨Subtype.val, continuous_subtype_val⟩)
      (fun x => hu x.val) = 0 := by
  unfold supportedWindingClass
  have hn := WindingSingular.singularWindingClass_naturality (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) u hu
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCohomologyRestriction (ModuleCat.of ℚ ℚ) X A 1
    (WindingSingular.singularWindingClass X u hu) =
    WindingSingular.singularWindingClass (TopCat.of A) (u.comp ⟨Subtype.val, continuous_subtype_val⟩)
      (fun x => hu x.val) at hn
  rw [← hn]
  exact ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCohomologyRestriction_connecting (ModuleCat.of ℚ ℚ) X A 1)
    (WindingSingular.singularWindingClass X u hu)

/-- Changing a local equation by an actual ambient unit preserves its
supported class; no compatibility of divisor or Chern classes is assumed. -/
theorem supportedWindingClass_mul_extending_unit (g : C(A, ℂ)) (hg : ∀ x, g x ≠ 0)
    (u : C(X, ℂ)) (hu : ∀ x, u x ≠ 0) :
    supportedWindingClass X A (g * (u.comp ⟨Subtype.val, continuous_subtype_val⟩))
      (fun x => mul_ne_zero (hg x) (hu x.val)) = supportedWindingClass X A g hg := by
  rw [supportedWindingClass_mul X A g _ hg (fun x => hu x.val),
    supportedWindingClass_extending_unit, add_zero]

/-- The local multiplicity survives multiplication by an actual extending unit. -/
theorem supportedWindingClass_unit_power (g f : C(A, ℂ))
    (hg : ∀ x, g x ≠ 0) (hf : ∀ x, f x ≠ 0)
    (u : C(X, ℂ)) (hu : ∀ x, u x ≠ 0) (m : ℤ)
    (hfg : ∀ x, f x = g x ^ m * u x.val) :
    supportedWindingClass X A f hf = m • supportedWindingClass X A g hg := by
  let v := WindingCech.RationalCech.nonvanishingPower (TopCat.of A) g hg m
  have hv : ∀ x, v x ≠ 0 := fun x => zpow_ne_zero m (hg x)
  have hfun : f = v * (u.comp ⟨Subtype.val, continuous_subtype_val⟩) := ContinuousMap.ext hfg
  subst f
  rw [supportedWindingClass_mul_extending_unit X A v hv u hu]
  exact supportedWindingClass_int_power X A g v hg hv m (fun _ => rfl)

/-- Forgetting support kills the connecting class of a single global equation. -/
theorem supportedWindingClass_absolute_zero (g : C(A, ℂ)) (hg : ∀ x, g x ≠ 0) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X A 2
      (supportedWindingClass X A g hg) = 0 :=
  ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting_inclusion (ModuleCat.of ℚ ℚ) X A 1)
    (WindingSingular.singularWindingClass (TopCat.of A) g hg)

/-- Pullback of pairs preserves the supported class of the actual composite function. -/
theorem supportedWindingClass_pullback {Y : TopCat.{0}} (f : Y ⟶ X) (B : Set Y)
    (hBA : Set.MapsTo f B A) (g : C(A, ℂ)) (hg : ∀ x, g x ≠ 0) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hBA 2
        (supportedWindingClass X A g hg) =
      supportedWindingClass Y B (g.comp (CycleClass.Geometric.LocalHomology.Cycles.subspaceMap f hBA).hom)
        (fun x => hg (CycleClass.Geometric.LocalHomology.Cycles.subspaceMap f hBA x)) := by
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting_naturality (ModuleCat.of ℚ ℚ) f hBA 1)
    (WindingSingular.singularWindingClass (TopCat.of A) g hg)
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hBA 2
      (supportedWindingClass X A g hg) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting (ModuleCat.of ℚ ℚ) Y B 1
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (CycleClass.Geometric.LocalHomology.Cycles.subspaceMap f hBA) 1
        (WindingSingular.singularWindingClass (TopCat.of A) g hg)) at h
  rw [WindingSingular.singularWindingClass_naturality] at h
  exact h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.Winding
