import OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteNormalHilbertBounds
import OAI.AlgebraicGeometry.SheafCohomology.Projective.IntrinsicDegree
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedTwistSections
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialComparison
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PushforwardCoherence

/-! # Pushforward Hilbert -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PushforwardHilbert

noncomputable section

/-! Actual Hilbert polynomials of finite normal pushforwards have the
intrinsic dimension and the function-field degree as their leading multiplier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

universe u
attribute [local instance] MvPolynomial.gradedAlgebra AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory

theorem degree_leadingCoeff_of_sections
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {σ : Type} [Fintype σ] [LinearOrder σ]
    (hfield : IsField Γ(Spec (.of R), ⊤))
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (g : X ⟶ Z) [IsFinite g] [IsDominant g]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (a : Z ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion a] (j : σ)
    [Nonempty (a ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)] [Nonempty ((g ≫ a) ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)]
    (P Q : Polynomial ℚ) (b : ℕ)
    (hP : ∀ n, b ≤ n →
      (Module.finrank Γ(Spec (.of R), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
        ((Scheme.Modules.pullback a).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n))) : ℚ) = P.eval (n : ℚ))
    (hQ : ∀ n, b ≤ n →
      (Module.finrank Γ(Spec (.of R), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
        ((Scheme.Modules.pushforward g).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) ⊗
          (Scheme.Modules.pullback a).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n))) : ℚ) = Q.eval (n : ℚ)) :
    letI := AlgebraicGeometry.SheafCohomology.Projective.DominantFunctionField.Dimension.dominantFunctionFieldAlgebra g
    Q.natDegree = P.natDegree ∧
      Q.leadingCoeff = (Module.finrank Z.functionField X.functionField : ℚ) * P.leadingCoeff := by
  let := AlgebraicGeometry.SheafCohomology.Projective.DominantFunctionField.Dimension.dominantFunctionFieldAlgebra g
  let D := Module.finrank Z.functionField X.functionField
  have hD : (0 : ℚ) < D := by
    have : Nonempty (g ⁻¹ᵁ a ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) := by
      rw [← Scheme.Hom.comp_preimage]
      infer_instance
    let := AlgebraicGeometry.SheafCohomology.Projective.FiniteFunctionField.Dimension.finite_dominant_functionField_finite g hX (a ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
      ((AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen j).preimage a)
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank Z.functionField X.functionField)
  have hp := AlgebraicGeometry.SheafCohomology.Projective.HilbertDimension.Dimension.closedProjective_Hilbert_leadingCoeff_pos hfield a j P b hP
  obtain ⟨c, s, hlo, hhi⟩ := AlgebraicGeometry.SheafCohomology.Projective.FiniteNormalHilbertBounds.Dimension.finiteNormalProjective_Hilbert_shift_bounds hfield g hX a j P Q b hP hQ
  have hq : Q ≠ 0 := by
    intro hz
    obtain ⟨t, ht⟩ := AlgebraicGeometry.FormalGeometry.Completion.PolynomialPositivity.Construction.polynomial_eventually_nat_pos_of_leadingCoeff_pos P hp
    have h := hlo (max c t) (le_max_left _ _)
    have hp' := mul_pos hD (ht (max c t) (le_max_right _ _))
    rw [hz, Polynomial.eval_zero] at h
    exact (not_le_of_gt hp') h
  have hqpos := AlgebraicGeometry.FormalGeometry.Completion.PolynomialPositivity.Construction.polynomial_leadingCoeff_pos_of_eventual_nat_nonneg Q hq b
    (fun n hn => by rw [← hQ n hn]; positivity)
  have hDP : 0 < (Polynomial.C (D : ℚ) * P).leadingCoeff := by
    simpa only [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C] using mul_pos hD hp
  obtain ⟨hd, hl⟩ := AlgebraicGeometry.FormalGeometry.Completion.PolynomialComparison.Construction.polynomial_degree_leadingCoeff_eq_of_mutual_shift_bounds
    (Polynomial.C (D : ℚ) * P) Q hDP hqpos c s
    (fun n hn => by simpa only [Polynomial.eval_mul, Polynomial.eval_C] using hlo n hn)
    (fun n hn => by simpa only [Polynomial.eval_mul, Polynomial.eval_C] using hhi n hn)
  exact ⟨by simpa only [Polynomial.natDegree_C_mul hD.ne'] using hd.symm,
    by simpa only [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C] using hl.symm⟩

variable {K : Type u} [Field K] {r : ℕ} {X Z : Scheme.{u}}

theorem closedHilbert_spec
    (a : Z ⟶ Proj (homogeneousSubmodule (Fin (r + 1)) K)) [IsClosedImmersion a]
    (M : Z.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (j : Fin (r + 1)) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      (Module.finrank Γ(Spec (.of K), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
        (M ⊗ (Scheme.Modules.pullback a).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n))) : ℚ) =
      (AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial a M j).eval (n : ℚ) := by
  obtain ⟨b, hb⟩ := AlgebraicGeometry.FormalGeometry.Completion.Projective.Numerics.Construction.projectiveHilbertPolynomial_spec (AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.coherentClosedDirectImage a M) j
  refine ⟨b, fun n hn => ?_⟩
  exact (congrArg (fun d : ℕ => (d : ℚ))
    (AlgebraicGeometry.SheafCohomology.Projective.ClosedTwistSections.MvPolynomial.closedImmersion_projectiveTwist_sectionsLinearEquiv a M j n).finrank_eq).trans (hb n hn)

theorem closedHilbert_spec_coordinate
    (a : Z ⟶ Proj (homogeneousSubmodule (Fin (r + 1)) K)) [IsClosedImmersion a]
    (M : Z.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (j k : Fin (r + 1)) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      (Module.finrank Γ(Spec (.of K), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
        (M ⊗ (Scheme.Modules.pullback a).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower k n))) : ℚ) =
      (AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial a M j).eval (n : ℚ) := by
  obtain ⟨b, hb⟩ := closedHilbert_spec a M j
  refine ⟨b, fun n hn => ?_⟩
  let e := (Scheme.Modules.pullback a).mapIso (AlgebraicGeometry.SheafCohomology.Projective.CoordinateBundleIso.Dimension.projectiveTwistCoordinateIso (R := K) j k n)
  exact (congrArg (fun d : ℕ => (d : ℚ))
    ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).mapIso
      (Iso.refl M ⊗ᵢ e)).toLinearEquiv.finrank_eq).symm.trans (hb n hn)

local instance unit_quasicoherent (Y : Scheme.{u}) :
    (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y).IsQuasicoherent :=
  ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleQuasicoherent.Construction.isQuasicoherent_of_isLineBundle _ (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_structureSheaf Y)

local instance unit_finiteType (Y : Scheme.{u}) :
    (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y).IsFiniteType :=
  AlgebraicGeometry.SheafCohomology.Projective.PolynomialQuotient.Dimension.isFiniteType_of_isLineBundle _ (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_structureSheaf Y)

local instance pushforwardUnit_quasicoherent (g : X ⟶ Z) [IsFinite g] :
    ((Scheme.Modules.pushforward g).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)).IsQuasicoherent :=
  AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom g

local instance pushforwardUnit_finiteType (g : X ⟶ Z) [IsFinite g] :
    ((Scheme.Modules.pushforward g).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)).IsFiniteType :=
  PushforwardCoherence.finiteType g (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)

theorem structure_degree_pos
    [IsIntegral Z]
    (a : Z ⟶ Proj (homogeneousSubmodule (Fin (r + 1)) K)) [IsClosedImmersion a]
    (ρ : Z ⟶ Spec (.of K)) [LocallyOfFiniteType ρ] (j : Fin (r + 1)) :
    let P := AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial a (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Z) j
    P.natDegree = AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension ρ ∧ 0 < P.leadingCoeff := by
  obtain ⟨b, hb⟩ := closedHilbert_spec a (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Z) j
  apply AlgebraicGeometry.SheafCohomology.Projective.IntrinsicDegree.Dimension.closedProjective_Hilbert_intrinsicDegree ρ AlgebraicGeometry.FormalGeometry.Completion.Projective.Numerics.Construction.fieldSpec_sections_isField a j _ b
  intro n hn
  exact (congrArg (fun d : ℕ => (d : ℚ))
    ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).mapIso
      (AlgebraicGeometry.SheafCohomology.Projective.PolynomialQuotient.Dimension.structureModuleTensorLeftIso ((Scheme.Modules.pullback a).obj
        (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n)))).toLinearEquiv.finrank_eq).symm.trans (hb n hn)

theorem finitePushforward_degree_leadingCoeff
    [IsIntegral X] [IsIntegral Z]
    (g : X ⟶ Z) [IsFinite g] [IsDominant g]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (a : Z ⟶ Proj (homogeneousSubmodule (Fin (r + 1)) K)) [IsClosedImmersion a]
    (ρ : Z ⟶ Spec (.of K)) [LocallyOfFiniteType ρ] (j : Fin (r + 1)) :
    letI := AlgebraicGeometry.SheafCohomology.Projective.DominantFunctionField.Dimension.dominantFunctionFieldAlgebra g
    let P := AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial a (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Z) j
    let Q := AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial a
      ((Scheme.Modules.pushforward g).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)) j
    Q.natDegree = AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension ρ ∧
      Q.leadingCoeff = (Module.finrank Z.functionField X.functionField : ℚ) * P.leadingCoeff := by
  let := AlgebraicGeometry.SheafCohomology.Projective.DominantFunctionField.Dimension.dominantFunctionFieldAlgebra g
  let P := AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial a (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Z) j
  let Q := AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial a
    ((Scheme.Modules.pushforward g).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)) j
  let z : Z := Classical.choice inferInstance
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show a z ∈ ⨆ k : Fin (r + 1), AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) k by
      rw [AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]; trivial)
  have : Nonempty (a ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen k) := ⟨⟨z, hk⟩⟩
  have : Nonempty ((g ≫ a) ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen k) := by
    refine ⟨⟨genericPoint X, ?_⟩⟩
    change g (genericPoint X) ∈ a ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen k
    rw [AlgebraicGeometry.SheafCohomology.Projective.DominantFunctionField.Dimension.dominant_genericPoint g]
    exact ((genericPoint_spec Z).mem_open_set_iff (a ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen k).isOpen).mpr
      (by simpa using (show Nonempty (a ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen k) from inferInstance))
  obtain ⟨b, hb⟩ := closedHilbert_spec_coordinate a (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Z) j k
  obtain ⟨c, hc⟩ := closedHilbert_spec_coordinate a
    ((Scheme.Modules.pushforward g).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)) j k
  have hP (n : ℕ) (hn : max b c ≤ n) :
      (Module.finrank Γ(Spec (.of K), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj
        ((Scheme.Modules.pullback a).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower k n))) : ℚ) =
      P.eval (n : ℚ) := by
    exact (congrArg (fun d : ℕ => (d : ℚ))
      ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).mapIso
        (AlgebraicGeometry.SheafCohomology.Projective.PolynomialQuotient.Dimension.structureModuleTensorLeftIso ((Scheme.Modules.pullback a).obj
          (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower k n)))).toLinearEquiv.finrank_eq).symm.trans
      (hb n ((le_max_left _ _).trans hn))
  have hQ := fun n hn => hc n ((le_max_right b c).trans hn)
  have hd := degree_leadingCoeff_of_sections AlgebraicGeometry.FormalGeometry.Completion.Projective.Numerics.Construction.fieldSpec_sections_isField g hX a k P Q
    (max b c) hP hQ
  have hPdim := structure_degree_pos a ρ j
  exact ⟨hd.1.trans hPdim.1, hd.2⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PushforwardHilbert
