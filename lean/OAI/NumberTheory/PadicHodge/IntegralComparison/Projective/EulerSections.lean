import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Numerics
import OAI.AlgebraicGeometry.SheafCohomology.Projective.SerreVanishing
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseZeroSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections

/-! # Euler Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.EulerSections.K

noncomputable section

/-! The actual projective Euler characteristic equals the dimension of
global sections after a sufficiently positive twist, over every field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace MonoidalCategory

open OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Numerics.Construction

universe u
attribute [local instance] MvPolynomial.gradedAlgebra AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory

theorem projectiveEuler_eventually_sections
    {K : Type u} [Field K] {r : ℕ}
    (M : (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (j : Fin (r + 1)) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      (AlgebraicGeometry.SheafCohomology.Projective.Euler.MvPolynomial.projectiveSheafEuler
        (M ⊗ AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) j n) : ℚ) =
        AlgebraicGeometry.FormalGeometry.Completion.Projective.Numerics.Construction.projectiveHilbertFunction M j n := by
  classical
  let : Field Γ(Spec (CommRingCat.of K), ⊤) := AlgebraicGeometry.FormalGeometry.Completion.Projective.Numerics.Construction.fieldSpec_sections_isField.toField
  have hv (q : Fin r) :=
    AlgebraicGeometry.SheafCohomology.Projective.SerreVanishing.MvPolynomial.finiteType_eventually_orderedBaseCechComplex_exactAt_succ M j q.val
  choose b hb using hv
  refine ⟨Finset.univ.sup b, fun n hn => ?_⟩
  let N := M ⊗ AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) j n
  let π := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) (σ := Fin (r + 1))
  let U := AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := K) (σ := Fin (r + 1))
  have heuler : AlgebraicGeometry.SheafCohomology.Projective.Euler.MvPolynomial.projectiveSheafEuler N =
      (Module.finrank Γ(Spec (CommRingCat.of K), ⊤)
        ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π N U).homology 0) : ℤ) := by
    unfold AlgebraicGeometry.SheafCohomology.Projective.Euler.MvPolynomial.projectiveSheafEuler
    rw [Finset.sum_eq_single 0]
    · simp only [pow_zero, one_mul]
      rfl
    · intro q hq hq0
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
      have hk : k < r := by have := Finset.mem_range.mp hq; omega
      have hn' : b ⟨k, hk⟩ ≤ n :=
        (Finset.le_sup (f := b) (Finset.mem_univ ⟨k, hk⟩)).trans hn
      have : Subsingleton
          ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π N U).homology (k + 1)) :=
        ModuleCat.subsingleton_of_isZero (hb ⟨k, hk⟩ n hn').isZero_homology
      rw [Module.finrank_zero_of_subsingleton]
      simp only [Nat.cast_zero, mul_zero]
    · simp
  have hU : IsOpenCover U :=
    IsOpenCover.mk (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top
      (R := K) (σ := Fin (r + 1)))
  let := AlgebraicGeometry.SheafCohomology.Projective.BaseZeroSections.baseGlobalSectionsModule π N
  rw [heuler, Int.cast_natCast]
  exact congrArg (fun d : ℕ => (d : ℚ))
    (AlgebraicGeometry.SheafCohomology.Projective.BaseZeroSections.orderedBaseCechHZeroGlobalSectionsLinearEquiv π N U hU).finrank_eq

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.EulerSections.K
