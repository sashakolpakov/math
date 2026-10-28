import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeChainD
import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.DualNormalization

/-! # Rational Local Purity -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RationalLocalPurity.Cycles

noncomputable section

/-!
# Rational local cohomology of complex normal coordinates

The cochain complex is the actual kernel of singular-cochain restriction to
the punctured space. Its cohomology is identified, through the proved relative
evaluation isomorphism, with the dual of the actual rational relative homology.
Exact rationalization of the integral local calculation then gives `ℚ` in
degree `2p` and zero in every other degree.

The distinguished class is dual to the specified integral-to-rational local
homology normalization. Its evaluation is proved to be one. Compatibility
with geometric orientations and nonlinear changes of normal charts is a
separate obligation, and no global Thom or algebraic-cycle class is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- The genuine relative rational cohomology of the punctured complex model. -/
abbrev complexNormalRationalLocalCohomology (p n : ℕ) : ModuleCat.{0} ℚ :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin p → ℂ))
    ({0}ᶜ : Set (Fin p → ℂ)) n

/-- The established rational top local homology normalization, as a linear equivalence. -/
def complexNormalRationalTopHomologyEquiv (p : ℕ) :
    RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of (Fin p → ℂ)) 0 (2 * p) ≃ₗ[ℚ] ℚ :=
  (RationalRelativeHomology.Cycles.complexNormalRationalTopLocalHomologyIso p).toLinearEquiv

/-- The rational homology generator specified by the integral local calculation
and its exact coefficient change. -/
def complexNormalRationalTopHomologyGenerator (p : ℕ) :
    RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of (Fin p → ℂ)) 0 (2 * p) :=
  (complexNormalRationalTopHomologyEquiv p).symm 1

@[simp]
theorem complexNormalRationalTopHomologyGenerator_normalization (p : ℕ) :
    complexNormalRationalTopHomologyEquiv p (complexNormalRationalTopHomologyGenerator p) = 1 :=
  (complexNormalRationalTopHomologyEquiv p).apply_symm_apply 1

/-- Top relative rational cohomology is `ℚ`, by actual evaluation on the
specified rational local homology generator. -/
def complexNormalRationalTopCohomologyEquiv (p : ℕ) :
    complexNormalRationalLocalCohomology p (2 * p) ≃ₗ[ℚ] ℚ :=
  (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of (Fin p → ℂ))
    ({0}ᶜ : Set (Fin p → ℂ)) (2 * p)).trans
      (DualNormalization.Cycles.dualNormalizationEquiv (complexNormalRationalTopHomologyEquiv p))

/-- The normalization map is explicitly evaluation on the actual generator. -/
theorem complexNormalRationalTopCohomologyEquiv_apply (p : ℕ)
    (a : complexNormalRationalLocalCohomology p (2 * p)) :
    complexNormalRationalTopCohomologyEquiv p a =
      RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of (Fin p → ℂ))
        ({0}ᶜ : Set (Fin p → ℂ)) (2 * p) a
          (complexNormalRationalTopHomologyGenerator p) := rfl

/-- The same genuine top cohomology computation in the category of rational modules. -/
def complexNormalRationalTopCohomologyIso (p : ℕ) :
    complexNormalRationalLocalCohomology p (2 * p) ≅ ModuleCat.of ℚ ℚ :=
  (complexNormalRationalTopCohomologyEquiv p).toModuleIso

/-- All other relative cohomology degrees vanish, including the low degrees. -/
theorem complexNormalRationalLocalCohomology_isZero (p n : ℕ) (hn : n ≠ 2 * p) :
    IsZero (complexNormalRationalLocalCohomology p n) := by
  have hH := RationalRelativeHomology.Cycles.complexNormalRationalLocalHomology_isZero p n hn
  have hdual := DualNormalization.Cycles.dual_isZero_of_isZero hH
  exact hdual.of_iso
    (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of (Fin p → ℂ))
      ({0}ᶜ : Set (Fin p → ℂ)) n).toModuleIso

/-- The distinguished local rational class is the inverse image of one under
the genuine evaluation normalization. -/
def complexNormalRationalDualClass (p : ℕ) :
    complexNormalRationalLocalCohomology p (2 * p) :=
  (complexNormalRationalTopCohomologyEquiv p).symm 1

@[simp]
theorem complexNormalRationalDualClass_normalization (p : ℕ) :
    complexNormalRationalTopCohomologyEquiv p (complexNormalRationalDualClass p) = 1 :=
  (complexNormalRationalTopCohomologyEquiv p).apply_symm_apply 1

/-- The class evaluates to one on the specified rational local homology generator. -/
theorem complexNormalRationalDualClass_evaluation (p : ℕ) :
    RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of (Fin p → ℂ))
      ({0}ᶜ : Set (Fin p → ℂ)) (2 * p) (complexNormalRationalDualClass p)
        (complexNormalRationalTopHomologyGenerator p) = 1 :=
  complexNormalRationalDualClass_normalization p

/-- Its full evaluation functional is the actual normalized local homology coordinate. -/
theorem complexNormalRationalDualClass_functional (p : ℕ) :
    RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of (Fin p → ℂ))
      ({0}ᶜ : Set (Fin p → ℂ)) (2 * p) (complexNormalRationalDualClass p) =
        (complexNormalRationalTopHomologyEquiv p).toLinearMap := by
  apply (DualNormalization.Cycles.dualNormalizationEquiv (complexNormalRationalTopHomologyEquiv p)).injective
  rw [DualNormalization.Cycles.dualNormalizationEquiv_toLinearMap]
  exact complexNormalRationalDualClass_normalization p

/-- Evaluation one uniquely characterizes the normalized local rational class. -/
theorem complexNormalRationalDualClass_unique (p : ℕ)
    (a : complexNormalRationalLocalCohomology p (2 * p))
    (ha : RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of (Fin p → ℂ))
      ({0}ᶜ : Set (Fin p → ℂ)) (2 * p) a
        (complexNormalRationalTopHomologyGenerator p) = 1) :
    a = complexNormalRationalDualClass p := by
  apply (complexNormalRationalTopCohomologyEquiv p).injective
  exact ha.trans (complexNormalRationalDualClass_normalization p).symm

theorem complexNormalRationalDualClass_ne_zero (p : ℕ) :
    complexNormalRationalDualClass p ≠ 0 := by
  intro h
  have hn := complexNormalRationalDualClass_normalization p
  rw [h, map_zero] at hn
  exact zero_ne_one hn

/-- Every top-degree local rational class is a unique rational multiple of
the normalized dual class. -/
theorem complexNormalRationalDualClass_generates (p : ℕ)
    (a : complexNormalRationalLocalCohomology p (2 * p)) :
    ∃! q : ℚ, q • complexNormalRationalDualClass p = a := by
  have hnorm (q : ℚ) :
      complexNormalRationalTopCohomologyEquiv p (q • complexNormalRationalDualClass p) = q := by
    rw [map_smul, complexNormalRationalDualClass_normalization]
    exact mul_one q
  refine ⟨complexNormalRationalTopCohomologyEquiv p a, ?_, ?_⟩
  · apply (complexNormalRationalTopCohomologyEquiv p).injective
    exact hnorm _
  · intro q hq
    calc
      q = complexNormalRationalTopCohomologyEquiv p
          (q • complexNormalRationalDualClass p) := (hnorm q).symm
      _ = complexNormalRationalTopCohomologyEquiv p a :=
        congrArg (complexNormalRationalTopCohomologyEquiv p) hq

/-- The top relative cohomology group is nonzero. -/
theorem complexNormalRationalTopCohomology_not_isZero (p : ℕ) :
    ¬ IsZero (complexNormalRationalLocalCohomology p (2 * p)) := by
  intro h
  let : Subsingleton (complexNormalRationalLocalCohomology p (2 * p)) :=
    ModuleCat.subsingleton_of_isZero h
  exact complexNormalRationalDualClass_ne_zero p (Subsingleton.elim _ _)

/-- Precise rational local purity in every degree, with no omitted zero-dimensional case. -/
theorem complexNormalRationalLocalCohomology_isZero_iff (p n : ℕ) :
    IsZero (complexNormalRationalLocalCohomology p n) ↔ n ≠ 2 * p := by
  constructor
  · intro h hn
    subst n
    exact complexNormalRationalTopCohomology_not_isZero p h
  · exact complexNormalRationalLocalCohomology_isZero p n

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RationalLocalPurity.Cycles
