import OAI.AlgebraicGeometry.CycleClass.Geometric.ProjectivePresentation
import OAI.AlgebraicGeometry.Divisors.LineBundles.Ord
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Chow.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: rational equivalence and the rational Chow quotient

The generators below are principal divisors of nonzero rational functions
on the actual reduced integral closed subschemes of codimension one less.
Their multiplicities are `Scheme.ord`, defined using lengths of local-ring
quotients. Equality of coefficients is required at every scheme point,
including points outside the requested codimension. No cohomological
condition enters the definition of rational equivalence.

The cycle-class descent and refined intersection pullback are separate
constructions; this file does not assume their existence or compatibility.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

/-- The generic-point indexing of the existing finite cycle group. -/
def cyclePointEmbedding (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :
    X.DimensionCycleSupport p ↪ X.carrier where
  toFun Z := irreducibleSetEquivPoints Z.1
  inj' := fun _ _ h => Subtype.ext (irreducibleSetEquivPoints.injective h)

/-- The coefficients of a graded cycle, extended by zero to all scheme points. -/
def pointCycle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (z : X.RationalDimensionCycle p) : X.carrier →₀ ℚ :=
  Finsupp.embDomain (cyclePointEmbedding X p) z

@[simp]
theorem pointCycle_apply (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (z : X.RationalDimensionCycle p) (Z : X.DimensionCycleSupport p) :
    pointCycle X p z (cyclePointEmbedding X p Z) = z Z :=
  Finsupp.embDomain_apply_self _ _ _

theorem pointCycle_injective (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :
    Function.Injective (pointCycle X p) :=
  Finsupp.embDomain_injective _

/-- The integral reduced scheme supporting a potential rational-equivalence
generator is locally Noetherian, even when that support is singular. -/
instance supportNoetherian (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (W : IrreducibleCloseds X.carrier) :
    AlgebraicGeometry.IsNoetherian (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) :=
  (X.projective.reducedSupport W).isNoetherian

/-- The finite rational principal divisor pushed along the support inclusion.
Finiteness is proved for every rational function in `Divisors`. -/
def principalDivisorCycle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (W : IrreducibleCloseds X.carrier)
    (f : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) : X.carrier →₀ ℚ :=
  Finsupp.embDomain
    ⟨CycleClass.Geometric.GenericPoint.reducedSupportι W, (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective⟩
    ((Ord.BundleCycles.principalDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) f).mapRange
      (fun n : ℤ => (n : ℚ)) (Int.cast_zero))

/-- Push a principal-divisor coefficient function along the actual closed
immersion. Closed immersions preserve the residue fields, so no residue-degree
factor is needed. Coefficients outside the support are zero. -/
def principalDivisorCoefficients (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (W : IrreducibleCloseds X.carrier)
    (f : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) : X.carrier → ℚ :=
  Function.extend (CycleClass.Geometric.GenericPoint.reducedSupportι W)
    (fun x => ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).ord f x : ℚ)) 0

@[simp]
theorem principalDivisorCoefficients_at_support (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (W : IrreducibleCloseds X.carrier)
    (f : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (x : CycleClass.Geometric.GenericPoint.reducedSupportScheme W) :
    principalDivisorCoefficients X W f ((CycleClass.Geometric.GenericPoint.reducedSupportι W) x) =
      ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).ord f x : ℚ) :=
  (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective.extend_apply _ _ _

theorem principalDivisorCoefficients_off_support (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (W : IrreducibleCloseds X.carrier)
    (f : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (x : X.carrier)
    (hx : x ∉ (W : Set X.carrier)) :
    principalDivisorCoefficients X W f x = 0 := by
  apply Function.extend_apply'
  simpa only [← Set.mem_range, CycleClass.Geometric.GenericPoint.range_reducedSupportι] using hx

/-- The finite divisor has exactly the local-length multiplicities above. -/
theorem principalDivisorCycle_apply (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (W : IrreducibleCloseds X.carrier)
    (f : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (x : X.carrier) :
    principalDivisorCycle X W f x = principalDivisorCoefficients X W f x := by
  classical
  by_cases hx : x ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι W)
  · obtain ⟨y, rfl⟩ := hx
    rw [principalDivisorCoefficients_at_support]
    exact Finsupp.embDomain_apply_self _ _ _
  · rw [principalDivisorCoefficients_off_support X W f x
      (by simpa only [CycleClass.Geometric.GenericPoint.range_reducedSupportι] using hx)]
    exact Finsupp.embDomain_of_notMem_range _ _ _ hx

/-- Orders of products add, including after extension to ambient points. -/
theorem principalDivisorCoefficients_mul (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (W : IrreducibleCloseds X.carrier)
    (f g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hf : f ≠ 0) (hg : g ≠ 0) :
    principalDivisorCoefficients X W (f * g) =
      principalDivisorCoefficients X W f + principalDivisorCoefficients X W g := by
  classical
  funext x
  by_cases hx : x ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι W)
  · obtain ⟨y, rfl⟩ := hx
    simp only [Pi.add_apply, principalDivisorCoefficients_at_support,
      Scheme.ord_mul hf hg, Int.cast_add]
  · have hxW : x ∉ (W : Set X.carrier) := by
      simpa only [CycleClass.Geometric.GenericPoint.range_reducedSupportι] using hx
    simp only [Pi.add_apply, principalDivisorCoefficients_off_support X W _ x hxW,
      zero_add]

/-- A finite graded cycle is principal if its coefficients are exactly those
of the divisor of a nonzero function on an integral support one degree larger.
The equality is imposed at all scheme points, not only on selected supports. -/
def IsPrincipalDivisorQ (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (z : X.RationalDimensionCycle p) : Prop :=
  ∃ W : IrreducibleCloseds X.carrier, X.supportCodimension W + 1 = p ∧
    ∃ f : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField, f ≠ 0 ∧
      pointCycle X p z = principalDivisorCycle X W f

/-- Rational equivalence is generated by the geometric principal divisors. -/
def rationalEquivalenceQ (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :
    Submodule ℚ (X.RationalDimensionCycle p) :=
  Submodule.span ℚ {z | IsPrincipalDivisorQ X p z}

/-- Codimension-p algebraic cycles modulo rational equivalence over ℚ. -/
def ChowQ (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) : ModuleCat ℚ :=
  ModuleCat.of ℚ (X.RationalDimensionCycle p ⧸ rationalEquivalenceQ X p)

/-- The canonical quotient map from finite cycles to the rational Chow group. -/
def cycleToChowQ (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :
    X.RationalDimensionCycle p →ₗ[ℚ] ChowQ X p :=
  (rationalEquivalenceQ X p).mkQ

theorem cycleToChowQ_surjective (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :
    Function.Surjective (cycleToChowQ X p) :=
  (rationalEquivalenceQ X p).mkQ_surjective

theorem cycleToChowQ_eq_zero_iff (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (z : X.RationalDimensionCycle p) :
    cycleToChowQ X p z = 0 ↔ z ∈ rationalEquivalenceQ X p :=
  Submodule.Quotient.mk_eq_zero _

theorem cycleToChowQ_eq_iff (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (z w : X.RationalDimensionCycle p) :
    cycleToChowQ X p z = cycleToChowQ X p w ↔ z - w ∈ rationalEquivalenceQ X p :=
  Submodule.Quotient.eq _

theorem principalDivisor_mem_rationalEquivalenceQ
    (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) (z : X.RationalDimensionCycle p)
    (hz : IsPrincipalDivisorQ X p z) : z ∈ rationalEquivalenceQ X p :=
  Submodule.subset_span hz

theorem cycleToChowQ_principalDivisor
    (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) (z : X.RationalDimensionCycle p)
    (hz : IsPrincipalDivisorQ X p z) : cycleToChowQ X p z = 0 :=
  (cycleToChowQ_eq_zero_iff X p z).mpr
    (principalDivisor_mem_rationalEquivalenceQ X p z hz)

/-- No codimension-zero principal-divisor relations are imposed. -/
theorem rationalEquivalenceQ_zero (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    rationalEquivalenceQ X 0 = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro z ⟨W, hW, _⟩
  exact False.elim (Nat.noConfusion hW)

/-- The precise geometric condition still needed to descend the existing
cycle-class map. This proves the quotient's universal property; it does not
assert that the class of every principal divisor vanishes. -/
theorem geometricCycleClass_descent_iff (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :
    (∃ cl : ChowQ X p →ₗ[ℚ] X.rationalCohomology (p + p),
      cl.comp (cycleToChowQ X p) = X.geometricCycleClassMap p) ↔
    ∀ z : X.RationalDimensionCycle p, IsPrincipalDivisorQ X p z →
      X.geometricCycleClassMap p z = 0 := by
  constructor
  · rintro ⟨cl, hcl⟩ z hz
    rw [← hcl, LinearMap.comp_apply, cycleToChowQ_principalDivisor X p z hz,
      map_zero]
  · intro h
    have hker : rationalEquivalenceQ X p ≤ LinearMap.ker (X.geometricCycleClassMap p) := by
      apply Submodule.span_le.mpr
      intro z hz
      exact h z hz
    exact ⟨(rationalEquivalenceQ X p).liftQ (X.geometricCycleClassMap p) hker,
      (rationalEquivalenceQ X p).liftQ_mkQ _ _⟩

/-- A descended geometric class map, if constructed, is unique because every
Chow class has a finite-cycle representative. -/
theorem geometricCycleClass_descent_unique (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (cl₁ cl₂ : ChowQ X p →ₗ[ℚ] X.rationalCohomology (p + p))
    (h₁ : cl₁.comp (cycleToChowQ X p) = X.geometricCycleClassMap p)
    (h₂ : cl₂.comp (cycleToChowQ X p) = X.geometricCycleClassMap p) : cl₁ = cl₂ := by
  ext a
  obtain ⟨z, rfl⟩ := cycleToChowQ_surjective X p a
  exact LinearMap.congr_fun (h₁.trans h₂.symm) z

end

/-! The genuine embedding of codimension cycles into finite point
cycles, expressed as a linear map. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

def projectiveCyclePointMap (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :
    X.RationalDimensionCycle p →ₗ[ℚ] (X.carrier →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (cyclePointEmbedding X p)

theorem projectiveCyclePointMap_apply (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (z : X.RationalDimensionCycle p) : projectiveCyclePointMap X p z = pointCycle X p z :=
  (Finsupp.embDomain_eq_mapDomain (cyclePointEmbedding X p) z).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Chow.BundleCycles
