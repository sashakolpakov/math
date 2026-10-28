import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.FreeCoordinates

/-! # Free Degrees -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.FreeDegrees.ProjectiveCech

noncomputable section

/-! Homogeneous localization of a weighted free module is coordinatewise Laurent grading. -/

open _root_.MvPolynomial _root_.Module

universe u v w

variable {σ : Type u} [Fintype σ] [DecidableEq σ]
variable (R : Type v) [CommRing R] {ι : Type w} (w : ι → ℤ)

def weightedLaurentGrading (s : Finset σ) : ℤ → Submodule R (ι →₀ LaurentMonomials.ProjectiveCech.ChartLocalization R s) :=
  BasisGrading.GradedModules.basisPiece (Finsupp.basis (fun _ : ι => LaurentBasis.ProjectiveCech.laurentBasis R s))
    (fun p => LaurentDegree.ProjectiveCech.exponentDegree p.2.val + w p.1)

theorem mem_weightedLaurentGrading (s : Finset σ) (d : ℤ) (f : ι →₀ LaurentMonomials.ProjectiveCech.ChartLocalization R s) :
    f ∈ weightedLaurentGrading R w s d ↔ ∀ i, f i ∈ LaurentDegree.ProjectiveCech.laurentDegreeSubmodule R s (d - w i) := by
  rw [weightedLaurentGrading, BasisGrading.GradedModules.mem_basisPiece_iff]
  simp only [LaurentDegree.ProjectiveCech.mem_laurentDegreeSubmodule_iff, Finsupp.basis_repr]
  constructor
  · intro h i a ha
    apply h ⟨i, a⟩
    change LaurentDegree.ProjectiveCech.exponentDegree a.val + w i ≠ d
    omega
  · intro h p hp
    apply h p.1 p.2
    change LaurentDegree.ProjectiveCech.exponentDegree p.2.val + w p.1 ≠ d at hp
    omega

theorem freeLocalizedEquiv_degree (s : Finset σ) (d : ℤ)
    (x : Graded.ModuleRestriction.ProjectiveCech.ModuleChart R (ι →₀ MvPolynomial σ R) s)
    (hx : x ∈ Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R _ (WeightedFreeModules.GradedModules.weightedFreeGrading R w) s d) :
    ∀ i, FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s x i ∈ LaurentDegree.ProjectiveCech.laurentDegreeSubmodule R s (d - w i) := by
  obtain ⟨k, p, hp, rfl⟩ := (DegreePieces.GradedModules.mem_localizedDegreePiece_iff (WeightedFreeModules.GradedModules.polynomialIntegerGrading R)
    (WeightedFreeModules.GradedModules.weightedFreeGrading R w) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ)
    (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s) d x).mp hx
  intro i
  rw [FreeCoordinates.ProjectiveCech.freeLocalizedEquiv_fraction]
  apply Polynomial.FractionDegrees.ProjectiveCech.chartFractionLinearMap_homogeneous
  have h := (WeightedFreeModules.GradedModules.mem_weightedFreeGrading R w _ p).mp hp i
  have he : d + (k : ℤ) * (s.card : ℤ) - w i = d - w i + (k : ℤ) * (s.card : ℤ) := by ring
  exact he ▸ h

theorem single_laurent_in_localized_degree_image (s : Finset σ) (i : ι) (a : LaurentExponents.ProjectiveCech.LaurentExponent s) :
    Finsupp.single i (LaurentMonomials.ProjectiveCech.laurentMonomial R a) ∈
      (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (ι →₀ MvPolynomial σ R) (WeightedFreeModules.GradedModules.weightedFreeGrading R w) s
        (LaurentDegree.ProjectiveCech.exponentDegree a.val + w i)).map (FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s).toLinearMap := by
  classical
  let k := LaurentExponents.ProjectiveCech.denominatorBound a
  let p : MvPolynomial σ R := monomial (LaurentExponents.ProjectiveCech.numeratorExponent a k) 1
  have hp : p ∈ WeightedFreeModules.GradedModules.polynomialIntegerGrading R (LaurentDegree.ProjectiveCech.exponentDegree a.val + (k : ℤ) * (s.card : ℤ)) :=
    isWeightedHomogeneous_monomial _ _ _ (Polynomial.FractionDegrees.ProjectiveCech.numeratorExponent_weight a k le_rfl)
  have hs : Finsupp.single i p ∈ WeightedFreeModules.GradedModules.weightedFreeGrading R w
      (LaurentDegree.ProjectiveCech.exponentDegree a.val + w i + (k : ℤ) * (s.card : ℤ)) := by
    rw [WeightedFreeModules.GradedModules.mem_weightedFreeGrading]
    intro j
    by_cases hij : i = j
    · subst j
      rw [Finsupp.single_eq_same]
      have he : LaurentDegree.ProjectiveCech.exponentDegree a.val + w i + (k : ℤ) * (s.card : ℤ) - w i =
          LaurentDegree.ProjectiveCech.exponentDegree a.val + (k : ℤ) * (s.card : ℤ) := by ring
      rw [he]
      exact hp
    · rw [Finsupp.single_eq_of_ne (Ne.symm hij)]
      exact Submodule.zero_mem _
  refine ⟨Module.Fractions.GradedModules.moduleFractionMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) k (Finsupp.single i p),
    DegreePieces.GradedModules.moduleFractionMap_mem_degree (WeightedFreeModules.GradedModules.weightedFreeGrading R w) _ _ _ k _ hs, ?_⟩
  apply Finsupp.ext
  intro j
  rw [LinearEquiv.coe_coe, FreeCoordinates.ProjectiveCech.freeLocalizedEquiv_fraction]
  by_cases hij : i = j
  · subst j
    rw [Finsupp.single_eq_same, Finsupp.single_eq_same, LaurentBasis.ProjectiveCech.chartFractionLinearMap_apply]
    rfl
  · rw [Finsupp.single_eq_of_ne (Ne.symm hij), Finsupp.single_eq_of_ne (Ne.symm hij), map_zero]

theorem weightedLaurentGrading_le_localized_degree_image (s : Finset σ) (d : ℤ) :
    weightedLaurentGrading R w s d ≤
      (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (ι →₀ MvPolynomial σ R) (WeightedFreeModules.GradedModules.weightedFreeGrading R w) s d).map
        (FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s).toLinearMap := by
  apply Submodule.span_le.mpr
  rintro x ⟨⟨i, a⟩, ha, rfl⟩
  simp only [Finsupp.coe_basis, LaurentBasis.ProjectiveCech.laurentBasis_apply]
  exact ha ▸ single_laurent_in_localized_degree_image R w s i a

theorem freeLocalizedEquiv_degree_iff (s : Finset σ) (d : ℤ)
    (x : Graded.ModuleRestriction.ProjectiveCech.ModuleChart R (ι →₀ MvPolynomial σ R) s) :
    x ∈ Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R _ (WeightedFreeModules.GradedModules.weightedFreeGrading R w) s d ↔
      ∀ i, FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s x i ∈ LaurentDegree.ProjectiveCech.laurentDegreeSubmodule R s (d - w i) := by
  constructor
  · exact freeLocalizedEquiv_degree R w s d x
  · intro hx
    have hmem := (mem_weightedLaurentGrading R w s d _).mpr hx
    obtain ⟨y, hy, he⟩ := weightedLaurentGrading_le_localized_degree_image R w s d hmem
    exact (FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s).injective he ▸ hy

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.FreeDegrees.ProjectiveCech
