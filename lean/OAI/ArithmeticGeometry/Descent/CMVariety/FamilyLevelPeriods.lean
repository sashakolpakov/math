import OAI.ArithmeticGeometry.Descent.CMVariety.ChartTorsionReferences
import OAI.ArithmeticGeometry.Descent.CMVariety.LevelComparison

/-! # Family Level Periods -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.FamilyLevelPeriods.Abelian.FamilyPoints

noncomputable section

/-!
Full integral period frames and the proved local uniqueness of actual
torsion sections give fixed integer coordinates for every full-level
label throughout a neighborhood of the central fiber.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj _root_.Topology

theorem exists_family_level_period_coordinates
    {P V Index : Type} [TopologicalSpace P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype Index]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (parameter : P → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (p₀ : P)
    (exponential : ∀ p, V → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (parameter p).left).scheme)
    (H : LocalPeriod.Abelian.LocalPeriodFamily (fun p => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (parameter p).left).scheme)
      exponential (fun p => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
        (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (parameter p))) p₀)
    (hsurj : Function.Surjective (exponential p₀))
    (Λ : P → Submodule ℤ V) (hΛ : ∀ p v, v ∈ Λ p ↔ exponential p v = 1)
    (r : P → (Index → ℝ) →L[ℝ] V) (hr : ContinuousAt r p₀)
    (hb : ∀ᶠ p in 𝓝 p₀, ∃ b : Module.Basis Index ℤ (Λ p),
      ∀ i, (b i : V) = r p (Pi.single i 1))
    (n : ℕ) (hn : 0 < n) (level : G.FullLevel n)
    (hunique : ∀ z : ∀ p, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (parameter p).left).scheme,
      z p₀ = 1 →
      ContinuousAt (fun p => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
        (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (parameter p)) (z p)) p₀ →
      (∀ᶠ p in 𝓝 p₀, z p ^ n = 1) → ∀ᶠ p in 𝓝 p₀, z p = 1) :
    ∃ coordinates : Multiplicative (Fin (2 * g) → ZMod n) → Index → ℤ,
      ∀ᶠ p in 𝓝 p₀, ∀ a,
        exponential p ((n : ℝ)⁻¹ • r p (fun i => (coordinates a i : ℝ))) =
          ((level.pullback (parameter p).left).hom.app (.op (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))
            (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase a)).val := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨b₀, hb₀⟩ := hb.self_of_nhds
  let levelSection :=  fun a : Multiplicative (Fin (2 * g) → ZMod n) =>
    (level.hom.app (.op (Over.mk (𝟙 S.left))) (LocallyConstant.const S.left a)).val
  have hlevelSection (a : Multiplicative (Fin (2 * g) → ZMod n)) : levelSection a ^ n = 1 :=
    (level.hom.app (.op (Over.mk (𝟙 S.left))) (LocallyConstant.const S.left a)).property
  have hcoords (a : Multiplicative (Fin (2 * g) → ZMod n)) :
      ∃ z : Index → ℤ, exponential p₀ ((n : ℝ)⁻¹ • r p₀ (fun i => (z i : ℝ))) =
        FamilyTranslations.Abelian.FamilyPoints.fiberSection S G (levelSection a) (parameter p₀) :=
    TorsionPeriodCoordinates.Abelian.exists_integer_period_coordinates_of_torsion (exponential p₀) (H.zero p₀) (H.add p₀)
      hsurj (Λ p₀) (hΛ p₀) b₀ (r p₀).toLinearMap hb₀ n hn
      (FamilyTranslations.Abelian.FamilyPoints.fiberSection S G (levelSection a) (parameter p₀))
      (FamilyTranslations.Abelian.FamilyPoints.fiberSection_torsion S G (levelSection a) n (hlevelSection a) (parameter p₀))
  choose coordinates hc using hcoords
  refine ⟨coordinates, Filter.eventually_all.mpr (fun a => ?_)⟩
  let z := fun p => exponential p ((n : ℝ)⁻¹ • r p (fun i => (coordinates a i : ℝ)))
  have hz : ∀ᶠ p in 𝓝 p₀, z p ^ n = 1 := by
    filter_upwards [hb] with p hp
    obtain ⟨b, hbp⟩ := hp
    exact TorsionPeriodCoordinates.Abelian.torsion_of_integer_period_coordinates (exponential p) (H.zero p) (H.add p)
      (Λ p) (hΛ p) (r p).toLinearMap
      (fun i => (hbp i) ▸ (b i).property) n hn (coordinates a)
  have h := FamilyTranslations.Abelian.FamilyPoints.torsion_section_locally_eq_algebraic_of_unique S G parameter p₀ n hunique
    (levelSection a) (hlevelSection a) z (hc a) (H.continuousAt_divided_period r hr n (coordinates a)) hz
  exact h.mono (fun p hp => hp.trans
    (LevelComparison.Abelian.FamilyPoints.fullLevel_pullback_constant_section G level (parameter p) a).symm)

end

end OAI.ArithmeticGeometry.Descent.CMVariety.FamilyLevelPeriods.Abelian.FamilyPoints
