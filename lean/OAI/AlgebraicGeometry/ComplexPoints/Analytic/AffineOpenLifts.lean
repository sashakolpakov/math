import OAI.AlgebraicGeometry.Foundations.Scheme.OpenImmersionPoints
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointUnderlying
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Affine Open Lifts -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic

noncomputable section

/-!
# Local affine factorizations through open immersions

A map from an affine complex scheme whose selected point lies in an open
subscheme factors through that open subscheme on a principal neighborhood of
the selected point. The factorization is constructed in the category over
`Spec ℂ`, using the actual spectrum localization map and open-immersion lift.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- A selected prime has a principal neighborhood on which the affine map
lifts through the given open immersion, compatibly with the complex base. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.exists_localizationLift_of_prime_mem
    {U X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (i : U ⟶ X) [IsOpenImmersion i.left]
    (A : CommAlgCat ℂ) (g : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (p : PrimeSpectrum A)
    (hp : g.left p ∈ Set.range i.left) :
    ∃ a : A, a ∉ p.asIdeal ∧
      ∃ l : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Localization.Away a) ⟶ U,
        l ≫ i =
          Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (Localization.Away a)
            (Algebra.algHom ℂ A (Localization.Away a)) ≫ g := by
  have hopen : IsOpen (g.left ⁻¹' Set.range i.left) :=
    (IsOpenImmersion.isOpen_range i.left).preimage g.left.continuous
  obtain ⟨V, ⟨a, rfl⟩, ha, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := A)).exists_subset_of_mem_open
      hp hopen
  let j : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Localization.Away a) ⟶ Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A :=
    Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (Localization.Away a)
      (Algebra.algHom ℂ A (Localization.Away a))
  have hfactor : Set.range (j ≫ g).left ⊆ Set.range i.left := by
    rintro y ⟨q, rfl⟩
    change g.left (PrimeSpectrum.comap (algebraMap A (Localization.Away a)) q) ∈
      Set.range i.left
    apply hsub
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away a) a).le
      (Set.mem_range_self q)
  refine ⟨a, ha, Foundations.Scheme.OpenImmersionPoints.openImmersion_relativeLift i (j ≫ g) hfactor, ?_⟩
  exact Foundations.Scheme.OpenImmersionPoints.openImmersion_relativeLift_fac i (j ≫ g) hfactor

/-- A complex point mapping into an open subscheme has an ordinary principal
neighborhood whose entire affine localization map lifts to that open subscheme. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.exists_localizationLift
    {U X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (i : U ⟶ X) [IsOpenImmersion i.left]
    (A : CommAlgCat ℂ) (g : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)
    (hx : SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A g x ∈ Set.range (SchemePointHomeomorphs.schemeComplexPoints.map i)) :
    ∃ a : A, x a ≠ 0 ∧
      ∃ l : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Localization.Away a) ⟶ U,
        l ≫ i =
          Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (Localization.Away a)
            (Algebra.algHom ℂ A (Localization.Away a)) ≫ g := by
  have hp : g.left (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum (A := A) x) ∈ Set.range i.left := by
    obtain ⟨y, hy⟩ := hx
    refine ⟨SchemePointHomeomorphs.schemeComplexPoints.underlying y, ?_⟩
    simpa only [SchemePointHomeomorphs.schemeComplexPoints.underlying_map, SchemePointHomeomorphs.schemeComplexPoints.underlying_affinePointMap] using congrArg SchemePointHomeomorphs.schemeComplexPoints.underlying hy
  obtain ⟨a, ha, l, hl⟩ :=
    SchemePointHomeomorphs.schemeComplexPoints.exists_localizationLift_of_prime_mem i A g (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum (A := A) x) hp
  refine ⟨a, ?_, l, hl⟩
  exact ha

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic
