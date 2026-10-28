import OAI.AlgebraicGeometry.CycleClass.Geometric.Span

/-! # Regular Ambient Cohomology -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.RegularAmbientCohomology

noncomputable section

/-!
# Absolute cohomology across the actual singular boundary

The proved two adjacent supported-cohomology vanishings make ordinary
restriction from the projective manifold to the complement of the singular
boundary an isomorphism in the cycle degree. The absolute cycle class is
therefore uniquely specified by the actual absolute regular-locus Thom class.
No locally finite homology restriction or local contractibility of the singular
support is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

section

/-- Vanishing of the two actual relative groups makes the actual absolute
restriction map an isomorphism. -/
theorem subspaceCohomologyRestriction_isIso_of_relative_zero
    {R : Type} [Ring R] (C : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (h₀ : IsZero (Cohomology.Singular.RelativeSequence.relativeSingularCohomology C X A n))
    (h₁ : IsZero (Cohomology.Singular.RelativeSequence.relativeSingularCohomology C X A (n + 1))) :
    IsIso (Cohomology.Singular.RelativeSequence.subspaceCohomologyRestriction C X A n) := by
  let : Mono (Cohomology.Singular.RelativeSequence.subspaceCohomologyRestriction C X A n) :=
    (Cohomology.Singular.RelativeSequence.relativeCohomology_exact_absolute C X A n).mono_g (h₀.eq_of_src _ _)
  let : Epi (Cohomology.Singular.RelativeSequence.subspaceCohomologyRestriction C X A n) :=
    (Cohomology.Singular.RelativeSequence.relativeCohomology_exact_subspace C X A n).epi_f (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end

namespace DimensionCycleSupport

variable {V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- Ordinary singular-cohomology restriction along the actual open inclusion
of the complement of this support's singular boundary. -/
abbrev _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientCohomologyRestriction (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (n : ℕ) :
    V.rationalCohomology n ⟶
      Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace) n :=
  Cohomology.Singular.RelativeSequence.subspaceCohomologyRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
    Z.analyticSingularBoundaryᶜ n

/-- Both obstruction groups vanish by the established geometric singular-
boundary purity theorem. This is the actual absolute restriction map. -/
instance _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientCohomologyRestriction_two_mul_isIso
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    IsIso (Z.regularAmbientCohomologyRestriction (2 * p)) :=
  subspaceCohomologyRestriction_isIso_of_relative_zero
    (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace) Z.analyticSingularBoundaryᶜ (2 * p)
    Z.singularBoundaryRationalCohomology_two_mul_isZero
    Z.singularBoundaryRationalCohomology_two_mul_add_one_isZero

/-- The same actual map in the degree notation of the cycle-class API. -/
instance _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientCohomologyRestriction_add_self_isIso
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    IsIso (Z.regularAmbientCohomologyRestriction (p + p)) := by
  exact (congrArg (fun n => IsIso (Z.regularAmbientCohomologyRestriction n))
    (two_mul p)).mp Z.regularAmbientCohomologyRestriction_two_mul_isIso

/-- The canonical extension isomorphism is inverse to ordinary restriction;
it is not a separately supplied comparison between cohomology spaces. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientCohomologyIso (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    V.rationalCohomology (p + p) ≅
      Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace) (p + p) :=
  asIso (Z.regularAmbientCohomologyRestriction (p + p))

@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientCohomologyIso_hom (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.regularAmbientCohomologyIso.hom = Z.regularAmbientCohomologyRestriction (p + p) :=
  rfl

/-- The ordinary class on the regular ambient open set obtained by forgetting
the support of the genuine regular-locus Thom class. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAbsoluteThomClass (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace) (p + p) := by
  simpa only [two_mul] using
    (Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      (Set.range Z.regularComplementInclusion)ᶜ (2 * p) Z.regularThomClass)

/-- Forgetting support and then restricting the constructed cycle class gives
the actual regular-locus Thom class with its support forgotten. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientCohomologyRestriction_cycleClass
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.regularAmbientCohomologyRestriction (p + p) Z.rationalCycleClass =
      Z.regularAbsoluteThomClass := by
  have h := ConcreteCategory.congr_hom
    (Z.regularThomCohomologyRestriction_inclusion (ModuleCat.of ℚ ℚ) (2 * p))
    Z.rationalSupportedCycleClass
  change Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      (Set.range Z.regularComplementInclusion)ᶜ (2 * p)
      (Z.regularThomCohomologyRestriction (ModuleCat.of ℚ ℚ) (2 * p)
        Z.rationalSupportedCycleClass) =
    Z.regularAmbientCohomologyRestriction (2 * p)
      (Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (Set.range Z.analyticInclusion)ᶜ (2 * p) Z.rationalSupportedCycleClass) at h
  rw [Z.rationalSupportedCycleClass_regularPullback] at h
  let A : ℕ → Type := fun n => V.rationalCohomology n
  let B : ℕ → Type := fun n =>
    Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace) n
  let a : A (2 * p) := Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ)
    (TopCat.of V.analyticSpace) (Set.range Z.analyticInclusion)ᶜ (2 * p)
      Z.rationalSupportedCycleClass
  let b : B (2 * p) := Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ)
    (TopCat.of Z.regularAmbientSpace) (Set.range Z.regularComplementInclusion)ᶜ
      (2 * p) Z.regularThomClass
  have transport (i j : ℕ) (e : i = j) (c : A i) :
      Z.regularAmbientCohomologyRestriction j (cast (congrArg A e) c) =
        cast (congrArg B e) (Z.regularAmbientCohomologyRestriction i c) := by
    cases e
    rfl
  change Z.regularAmbientCohomologyRestriction (p + p)
      (cast (congrArg A (two_mul p)) a) = cast (congrArg B (two_mul p)) b
  exact (transport (2 * p) (p + p) (two_mul p) a).trans
    (congrArg (cast (congrArg B (two_mul p))) h.symm)

/-- The absolute extension of the regular Thom class is exactly the already
constructed absolute algebraic cycle class. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientCohomologyIso_inv_thom (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.regularAmbientCohomologyIso.inv Z.regularAbsoluteThomClass =
      Z.rationalCycleClass := by
  rw [← Z.regularAmbientCohomologyRestriction_cycleClass]
  exact Z.regularAmbientCohomologyIso.toLinearEquiv.symm_apply_apply Z.rationalCycleClass

/-- Ordinary cohomology classes on the whole ambient variety are determined
in this degree by their restriction away from the singular boundary. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientCohomologyRestriction_injective
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Function.Injective (Z.regularAmbientCohomologyRestriction (p + p)) :=
  Z.regularAmbientCohomologyIso.toLinearEquiv.injective

/-- No supported lift of the competing class is needed: equality on the
actual regular ambient open set already identifies the absolute class. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.rationalCycleClass_unique_of_regularRestriction
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (a : V.rationalCohomology (p + p))
    (ha : Z.regularAmbientCohomologyRestriction (p + p) a =
      Z.regularAbsoluteThomClass) :
    a = Z.rationalCycleClass :=
  Z.regularAmbientCohomologyRestriction_injective
    (ha.trans Z.regularAmbientCohomologyRestriction_cycleClass.symm)

/-- A full characterization using only actual absolute cohomology and
restriction along the open inclusion. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.eq_rationalCycleClass_iff_regularRestriction
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (a : V.rationalCohomology (p + p)) :
    a = Z.rationalCycleClass ↔
      Z.regularAmbientCohomologyRestriction (p + p) a =
        Z.regularAbsoluteThomClass := by
  constructor
  · rintro rfl
    exact Z.regularAmbientCohomologyRestriction_cycleClass
  · exact Z.rationalCycleClass_unique_of_regularRestriction a

end DimensionCycleSupport

end

end OAI.AlgebraicTopology.DeRham.Comparison.RegularAmbientCohomology
