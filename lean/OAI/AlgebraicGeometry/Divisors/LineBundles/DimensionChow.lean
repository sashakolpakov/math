import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.GlobalSpecialization
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Dimension Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChow.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: Chow groups for the nonprojective deformation schemes

These dimension-indexed Chow groups are quotients by the span of genuine
principal divisors on actual integral supports of dimension one larger.
They do not require smoothness, projectivity, or a purity assumption.
Specialization on the quotient requires a separate relation-preservation
proof; it is not included in the definitions.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme} [AlgebraicGeometry.IsNoetherian X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

/-- A principal-divisor generator in the actual dimension grading. -/
def IsDimensionPrincipalDivisorQ (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) : Prop :=
  ∃ W : IrreducibleCloseds X, Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1 ∧
    ∃ g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField, g ≠ 0 ∧
      z = Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d W g

/-- The defining generators have exactly the full principal-divisor coefficients at every point. -/
theorem isDimensionPrincipalDivisorQ_iff [LocallyOfFiniteType f] (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    IsDimensionPrincipalDivisorQ f d z ↔
      ∃ W : IrreducibleCloseds X, Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1 ∧
        ∃ g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField, g ≠ 0 ∧
          Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z = Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g := by
  constructor
  · rintro ⟨W, hW, g, hg, rfl⟩
    exact ⟨W, hW, g, hg, Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f d W hW g⟩
  · rintro ⟨W, hW, g, hg, hz⟩
    refine ⟨W, hW, g, hg, Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective f d ?_⟩
    exact hz.trans (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f d W hW g).symm

/-- Rational equivalence in dimension d on a general Noetherian scheme. -/
def dimensionRationalEquivalenceQ (d : ℕ) : Submodule ℚ (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :=
  Submodule.span ℚ {z | IsDimensionPrincipalDivisorQ f d z}

/-- The rational Chow group of dimension-d cycles on the actual scheme. -/
def DimensionChowQ (d : ℕ) : ModuleCat ℚ :=
  ModuleCat.of ℚ ((Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) ⧸ dimensionRationalEquivalenceQ f d)

def dimensionCycleToChowQ (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) →ₗ[ℚ] DimensionChowQ f d :=
  (dimensionRationalEquivalenceQ f d).mkQ

theorem dimensionCycleToChowQ_surjective (d : ℕ) : Function.Surjective (dimensionCycleToChowQ f d) :=
  (dimensionRationalEquivalenceQ f d).mkQ_surjective

theorem dimensionCycleToChowQ_eq_zero_iff (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    dimensionCycleToChowQ f d z = 0 ↔ z ∈ dimensionRationalEquivalenceQ f d :=
  Submodule.Quotient.mk_eq_zero _

/-- Every actual principal divisor of the required dimension vanishes in the quotient. -/
theorem dimensionCycleToChowQ_principal (d : ℕ) (W : IrreducibleCloseds X)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    dimensionCycleToChowQ f d (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d W g) = 0 :=
  (dimensionCycleToChowQ_eq_zero_iff f d _).mpr (Submodule.subset_span ⟨W, hW, g, hg, rfl⟩)

end

/-! # LineBundleCycles: canonical Chow transport along equality of actual structure morphisms -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} {f g : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}

def dimensionCycleTransport (h : f = g) (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint g d →₀ ℚ) := by
  subst g
  exact LinearMap.id

theorem dimensionCycleTransport_forget (h : f = g) (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion g d (dimensionCycleTransport h d z) = Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z := by
  subst g
  rfl

variable [AlgebraicGeometry.IsNoetherian X]

def dimensionChowTransport (h : f = g) (d : ℕ) : DimensionChowQ f d →ₗ[ℚ] DimensionChowQ g d := by
  subst g
  exact LinearMap.id

theorem dimensionChowTransport_cycle (h : f = g) (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    dimensionChowTransport h d (dimensionCycleToChowQ f d z) =
      dimensionCycleToChowQ g d (dimensionCycleTransport h d z) := by
  subst g
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChow.BundleCycles
