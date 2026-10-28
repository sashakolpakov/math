import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.CohomologyVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.FieldProjectivity

/-! # Field Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The positive-power graph-bundle vanishing theorem holds over every field, using the already proved descent of ampleness. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_positivePower_cohomology_vanishes_overField
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(Spec (.of K), ⊤))) (m : ℕ) (hm : 0 < m) (q : ℕ) :
    IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap A.abelian.scheme.hom)
      (q + 1)).obj (A.graphBundle.tensorPower m).sheaf) := by
  have : NeZero N := ⟨by omega⟩
  have := A.abelian.fullLevel_multiplication_isFinite A.level
  have : A.abelian.scheme.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from A.abelian.scheme.hom]
    infer_instance
  have hd : 1 < N * N := by
    have hh := Nat.mul_le_mul hN hN
    omega
  exact ExpandingLineBundleCohomology.ample_lineBundle_allPowers_vanish_of_expanding_pullback A.abelian.scheme.hom
    (A.abelian.multiplication N).left (A.abelian.multiplication N).w A.graphBundle
    A.graphBundle_isAmple_overField hd (A.graphBundle_multiplication_iso N).some
    (fun L => A.abelian.fullLevel_multiplication_lineBundleUnit_splitMono A.level hunit L) m hm q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
