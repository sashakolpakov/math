import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.FiniteFlatTopDimension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyEulerCharacteristic

/-! # Polarization Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Pulling Poincare back by the actual polarization gives cohomology in
degree g of dimension the specified polarization degree, and the corresponding Euler characteristic. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem PolarizationData.PolarizedAbelianWithFullLevel.poincarePolarization_cohomology
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    {P : Scheme.{u}} {a : P ⟶ (A.dual.abelian.scheme ⊗ A.abelian.scheme).left}
    {b : P ⟶ A.abelian.scheme.left}
    (H : IsPullback a b (pullback.fst A.dual.abelian.scheme.hom A.abelian.scheme.hom)
      A.polarization.isogeny.hom.left) :
    (∀ q : ℕ, q ≠ g → IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap (b ≫ A.abelian.scheme.hom)) q).obj (A.dual.poincare.pullback a).sheaf)) ∧
    Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap (b ≫ A.abelian.scheme.hom)) g).obj (A.dual.poincare.pullback a).sheaf) =
        (∏ i, δ i) ^ 2 := by
  have : IsProper A.abelian.scheme.hom := A.abelian.proper
  have : A.abelian.scheme.left.IsSeparated := ⟨by rw [← terminal.comp_from A.abelian.scheme.hom]; infer_instance⟩
  have : IsLocallyNoetherian A.abelian.scheme.left :=
    LocallyOfFiniteType.isLocallyNoetherian A.abelian.scheme.hom
  let t := A.polarization.isogeny.hom.left
  let z := η[A.dual.abelian.scheme].left (IsLocalRing.closedPoint K)
  obtain ⟨U, hUa, hz, _⟩ := exists_isAffineOpen_mem_and_subset
    (show z ∈ (⊤ : A.dual.abelian.scheme.left.Opens) from trivial)
  have hU : Set.range η[A.dual.abelian.scheme].left ⊆ U := by
    rintro y ⟨x, rfl⟩
    have he : η[A.dual.abelian.scheme].left x = z :=
      congrArg η[A.dual.abelian.scheme].left
        (@Subsingleton.elim (PrimeSpectrum K) inferInstance x (IsLocalRing.closedPoint K))
    exact he.symm ▸ hz
  have hcoho := A.poincare_finiteFlat_global_cohomology A.dual hg hN hNk t H U hUa hU
  have hdim := A.poincare_finiteFlat_top_finrank A.dual hg hN hNk t H
  have hbase : HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficientMap (b := b ≫ (t ≫ A.dual.abelian.scheme.hom)) =
      Coefficient.ModulePresheaf.schemeCoefficientMap (b ≫ A.abelian.scheme.hom) := by
    change Coefficient.ModulePresheaf.schemeCoefficientMap (b ≫ (t ≫ A.dual.abelian.scheme.hom)) = _
    rw [show t ≫ A.dual.abelian.scheme.hom = A.abelian.scheme.hom from A.polarization.isogeny.hom.w]
  rw [hbase] at hcoho hdim
  exact ⟨hcoho.1, hdim.trans (A.polarization.kernelType.degree z)⟩

theorem PolarizationData.PolarizedAbelianWithFullLevel.poincarePolarization_euler
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    {P : Scheme.{u}} {a : P ⟶ (A.dual.abelian.scheme ⊗ A.abelian.scheme).left}
    {b : P ⟶ A.abelian.scheme.left}
    (H : IsPullback a b (pullback.fst A.dual.abelian.scheme.hom A.abelian.scheme.hom)
      A.polarization.isogeny.hom.left) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (b ≫ A.abelian.scheme.hom) (A.dual.poincare.pullback a).sheaf =
      (-1 : ℤ) ^ g * ((∏ i, δ i : ℕ) : ℤ) ^ 2 := by
  obtain ⟨hvan, hdim⟩ := A.poincarePolarization_cohomology hg hN hNk H
  unfold CohomologyEulerCharacteristic.coefficientEulerCharacteristic
  rw [finsum_eq_single _ g]
  · rw [hdim, Nat.cast_pow]
  · intro q hq
    have : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
        (Coefficient.ModulePresheaf.schemeCoefficientMap (b ≫ A.abelian.scheme.hom)) q).obj (A.dual.poincare.pullback a).sheaf) :=
      ModuleCat.isZero_iff_subsingleton.mp (hvan q hq)
    simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
