import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicHolomorphicPeriods
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ContinuousPresentedPeriods

/-! # Intrinsic Family Period Matrices -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyPeriodMatrices

noncomputable section

/-! The actual normalized family charts construct holomorphic full
period matrices, with literal native markings, surjectivity, and the
same kernels as the original fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical ContDiff _root_.Manifold _root_.CategoryTheory.MonObj

local instance (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral B.toOver.left := B.variety.property
local instance (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth B.toOver.hom := B.variety.presentation.smooth

theorem exists_native_family_holomorphic_period_matrices
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    [CompleteSpace F] [FiniteDimensional ℂ F]
    (G : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (present : ∀ s : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback s.left))
    (V : (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G).left.Opens) (hV : IsAffineOpen V)
    {R : Type} [CommRing R] [Algebra ℂ R]
    [Algebra R (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V)]
    [IsScalarTower ℂ R (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V)]
    (b : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) [IsOpenImmersion b.left]
    (hi : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V hV ≫ ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G =
      Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V)
        (IsScalarTower.toAlgHom ℂ R (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V)) ≫ b)
    (σ : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V →ₐ[ℂ] R)
    (hσ : Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V) R σ ≫
          ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V hV = b ≫ ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.identitySection S G)
    {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V)}
    (N : ArithmeticGeometry.Descent.CMVariety.RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x σ) :
    let s := fun q : F => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap
      (CommAlgCat.of ℂ R) b (N.charts.base.symm q)
    ∃ (n d : ℕ) (U : Set F), IsOpen U ∧
      N.charts.base (x.comp (IsScalarTower.toAlgHom ℂ R
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V))) ∈ U ∧ U ⊆ N.neighborhood ∧
      ∃ (marking : ∀ q : U, ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Fin n) (present (s q)).variety)
        (coordinates : ∀ q : U, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (present (s q)).variety ≃L[ℂ] (Fin d → ℂ))
        (matrix : F → (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)),
        DifferentiableOn ℂ matrix U ∧
        (∀ q : U, matrix q = ((coordinates q).toLinearEquiv.toLinearMap.comp
          (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (marking q))).toContinuousLinearMap) ∧
        (∀ q : U, Function.Surjective (matrix q)) ∧
        ∀ q : U, (matrix q).ker = (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (marking q)).ker := by
  dsimp only
  let s := fun q : F => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap
    (CommAlgCat.of ℂ R) b (N.charts.base.symm q)
  let q₀ := N.charts.base (x.comp (IsScalarTower.toAlgHom ℂ R
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V)))
  let A := fun q : F => G.pullback (s q).left
  let (q : F) : IsIntegral (A q).scheme.left := (present (s q)).isIntegral
  let (q : F) : T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A q).scheme) := (present (s q)).t2Space
  obtain ⟨c, n, r, hc, _, U₀, hU₀, hqU₀, hr, hhol, hmark⟩ :=
    IntrinsicHolomorphicPeriods.IntrinsicFamilyPeriods.exists_native_holomorphic_full_period_bases G present V hV b hi σ hσ N
  let U := U₀ ∩ N.neighborhood
  have hU : IsOpen U := hU₀.inter N.isOpen
  have hqU : q₀ ∈ U := ⟨hqU₀, N.center⟩
  have hc' (q : F) (hq : q ∈ U) :
      (1 : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A q).scheme) ∈ (c q).source ∧ c q 1 = 0 ∧
      ContMDiffOn (𝓘(ℂ, ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel (A q))) (𝓘(ℂ, E)) 1 (c q) (c q).source ∧
      ContMDiffOn (𝓘(ℂ, E)) (𝓘(ℂ, ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel (A q))) 1 (c q).symm (c q).target := by
    obtain ⟨h1, h0, _, _, _, _, _, hf, hi'⟩ := hc q hq.2
    exact ⟨h1, h0, hf.of_le (by simp), hi'.of_le (by simp)⟩
  obtain ⟨d, e, T, marking, matrix, _, _, hmatrix, hmatrixHol⟩ :=
    ContinuousPresentedPeriods.exists_holomorphic_presented_periods_on A (fun q => present (s q)) c U hc' n r
      (fun q hq => hmark q hq.1) q₀ hqU (hr.mono inter_subset_left)
      (fun j => (hhol j).mono inter_subset_left)
  let coordinates := fun q : U => (T q).symm.trans e
  refine ⟨n, d, U, hU, hqU, inter_subset_right, marking, coordinates, matrix,
    hmatrixHol, hmatrix, ?_, ?_⟩
  · intro q
    rw [hmatrix q]
    change Function.Surjective (fun v => coordinates q (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (marking q) v))
    exact (coordinates q).surjective.comp (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap_surjective (marking q))
  · intro q
    ext v
    change matrix q v = 0 ↔ ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (marking q) v = 0
    rw [hmatrix q]
    change coordinates q (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (marking q) v) = 0 ↔ _
    exact (coordinates q).map_eq_zero_iff

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyPeriodMatrices
