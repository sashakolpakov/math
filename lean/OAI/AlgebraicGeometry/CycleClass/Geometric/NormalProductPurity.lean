import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalProductCohomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalLocalPurity

/-! # Normal Product Purity -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.NormalProductPurity

noncomputable section

/-!
# Rational purity and the normalized class of the actual normal product pair

The class is pulled back from the computed punctured complex normal model
along the actual normal projection. The pair contraction proves that this
pullback is an isomorphism. This gives the local product calculation needed
by normal charts, without postulating a global Thom class.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

namespace Cycles

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual rational relative cohomology of the product with a complex normal space. -/
abbrev complexNormalProductRationalCohomology (p n : ℕ) : ModuleCat.{0} ℚ :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (E × (Fin p → ℂ)))
    (NormalProductPair.Cycles.normalProductComplement E (Fin p → ℂ) 0) n

/-- The normalized top-degree coordinate comes from the actual normal projection. -/
def complexNormalProductRationalTopCohomologyEquiv (p : ℕ) :
    complexNormalProductRationalCohomology E p (2 * p) ≃ₗ[ℚ] ℚ :=
  (NormalProductCohomology.Cycles.normalProductCohomologyIso (ModuleCat.of ℚ ℚ) E (Fin p → ℂ) 0 (2 * p)).toLinearEquiv.symm.trans
    (RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyEquiv p)

/-- The same genuine product-pair calculation as an isomorphism of rational modules. -/
def complexNormalProductRationalTopCohomologyIso (p : ℕ) :
    complexNormalProductRationalCohomology E p (2 * p) ≅ ModuleCat.of ℚ ℚ :=
  (complexNormalProductRationalTopCohomologyEquiv E p).toModuleIso

/-- The normalized rational relative class of the normal product pair. -/
def complexNormalProductRationalClass (p : ℕ) :
    complexNormalProductRationalCohomology E p (2 * p) :=
  (complexNormalProductRationalTopCohomologyEquiv E p).symm 1

@[simp]
theorem complexNormalProductRationalClass_normalization (p : ℕ) :
    complexNormalProductRationalTopCohomologyEquiv E p
      (complexNormalProductRationalClass E p) = 1 :=
  (complexNormalProductRationalTopCohomologyEquiv E p).apply_symm_apply 1

/-- The normalized class is literally the pullback of the actual normal dual class. -/
theorem complexNormalProductRationalClass_eq_pullback (p : ℕ) :
    complexNormalProductRationalClass E p =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (NormalProductPair.Cycles.normalProductProjection E (Fin p → ℂ))
        (NormalProductPair.Cycles.normalProductProjection_mapsTo E (Fin p → ℂ) 0) (2 * p)).hom
          (RationalLocalPurity.Cycles.complexNormalRationalDualClass p) := rfl

/-- Restriction to every constant tangential fiber is the same normalized normal class. -/
theorem complexNormalProductRationalClass_fiber (p : ℕ) (e : E) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (NormalProductPair.Cycles.normalProductSection E (Fin p → ℂ) e)
      (NormalProductPair.Cycles.normalProductSection_mapsTo E (Fin p → ℂ) e 0) (2 * p)).hom
        (complexNormalProductRationalClass E p) = RationalLocalPurity.Cycles.complexNormalRationalDualClass p := by
  rw [complexNormalProductRationalClass_eq_pullback]
  exact ConcreteCategory.congr_hom
    (NormalProductCohomology.Cycles.normalProductCohomology_fiber (ModuleCat.of ℚ ℚ) E (Fin p → ℂ) e 0 (2 * p))
    (RationalLocalPurity.Cycles.complexNormalRationalDualClass p)

/-- On each normal fiber the class evaluates to one on the actual rationalized
integral local homology generator. -/
theorem complexNormalProductRationalClass_fiber_evaluation (p : ℕ) (e : E) :
    RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of (Fin p → ℂ))
      ({0}ᶜ : Set (Fin p → ℂ)) (2 * p)
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (NormalProductPair.Cycles.normalProductSection E (Fin p → ℂ) e)
        (NormalProductPair.Cycles.normalProductSection_mapsTo E (Fin p → ℂ) e 0) (2 * p)).hom
          (complexNormalProductRationalClass E p))
      (RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator p) = 1 := by
  rw [complexNormalProductRationalClass_fiber]
  exact RationalLocalPurity.Cycles.complexNormalRationalDualClass_evaluation p

/-- The computed normal product class is nonzero. -/
theorem complexNormalProductRationalClass_ne_zero (p : ℕ) :
    complexNormalProductRationalClass E p ≠ 0 := by
  intro h
  have hn := complexNormalProductRationalClass_normalization E p
  rw [h, map_zero] at hn
  exact zero_ne_one hn

/-- Every top-degree product-pair class is a unique rational multiple of this class. -/
theorem complexNormalProductRationalClass_generates (p : ℕ)
    (a : complexNormalProductRationalCohomology E p (2 * p)) :
    ∃! q : ℚ, q • complexNormalProductRationalClass E p = a := by
  have hnorm (q : ℚ) :
      complexNormalProductRationalTopCohomologyEquiv E p
        (q • complexNormalProductRationalClass E p) = q := by
    rw [map_smul, complexNormalProductRationalClass_normalization]
    exact mul_one q
  refine ⟨complexNormalProductRationalTopCohomologyEquiv E p a, ?_, ?_⟩
  · apply (complexNormalProductRationalTopCohomologyEquiv E p).injective
    exact hnorm _
  · intro q hq
    calc
      q = complexNormalProductRationalTopCohomologyEquiv E p
          (q • complexNormalProductRationalClass E p) := (hnorm q).symm
      _ = complexNormalProductRationalTopCohomologyEquiv E p a :=
        congrArg (complexNormalProductRationalTopCohomologyEquiv E p) hq

/-- Actual relative cohomology vanishes outside the normal real dimension. -/
theorem complexNormalProductRationalCohomology_isZero (p n : ℕ) (hn : n ≠ 2 * p) :
    IsZero (complexNormalProductRationalCohomology E p n) :=
  (RationalLocalPurity.Cycles.complexNormalRationalLocalCohomology_isZero p n hn).of_iso
    (NormalProductCohomology.Cycles.normalProductCohomologyIso (ModuleCat.of ℚ ℚ) E (Fin p → ℂ) 0 n).symm

/-- Top relative cohomology is nonzero, including codimension zero. -/
theorem complexNormalProductRationalTopCohomology_not_isZero (p : ℕ) :
    ¬ IsZero (complexNormalProductRationalCohomology E p (2 * p)) := by
  intro h
  let : Subsingleton (complexNormalProductRationalCohomology E p (2 * p)) :=
    ModuleCat.subsingleton_of_isZero h
  exact complexNormalProductRationalClass_ne_zero E p (Subsingleton.elim _ _)

/-- The precise purity statement for all degrees of the actual normal product pair. -/
theorem complexNormalProductRationalCohomology_isZero_iff (p n : ℕ) :
    IsZero (complexNormalProductRationalCohomology E p n) ↔ n ≠ 2 * p := by
  constructor
  · intro h hn
    subst n
    exact complexNormalProductRationalTopCohomology_not_isZero E p h
  · exact complexNormalProductRationalCohomology_isZero E p n

/-- The normalized class is invariant under every invertible complex normal matrix. -/
theorem complexNormalProductRationalClass_invariant (p : ℕ)
    (A : Matrix (Fin p) (Fin p) ℂ) (hA : IsUnit A) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalProductPair.Cycles.normalProductComplexChange E A)
      (NormalProductPair.Cycles.normalProductComplexChange_mapsTo E A hA) (2 * p)).hom
        (complexNormalProductRationalClass E p) = complexNormalProductRationalClass E p :=
  NormalProductCohomology.Cycles.normalProductComplexChange_class_invariant (ModuleCat.of ℚ ℚ) E A hA (2 * p)
    (complexNormalProductRationalClass E p)

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.NormalProductPurity
