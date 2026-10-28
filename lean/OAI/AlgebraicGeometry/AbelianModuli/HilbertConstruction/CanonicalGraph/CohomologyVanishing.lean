import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExpandingLineBundleCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.Quadratic
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LevelMultiplication.LineTrace

/-! # Cohomology Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every positive tensor power of the canonical polarized graph bundle has vanishing positive cohomology over an algebraically closed field at invertible full level. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_positivePower_cohomology_vanishes
    {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(Spec (.of K), ⊤))) (m : ℕ) (hm : 0 < m) (q : ℕ) :
    IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap A.abelian.scheme.hom)
      (q + 1)).obj (A.graphBundle.tensorPower m).sheaf) := by
  have : NeZero N := ⟨by omega⟩
  have := A.abelian.fullLevel_multiplication_isFinite A.level
  have hsep : A.abelian.scheme.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from A.abelian.scheme.hom]
    infer_instance
  have hd : 1 < N * N := by
    have hh := Nat.mul_le_mul hN hN
    omega
  exact ExpandingLineBundleCohomology.ample_lineBundle_allPowers_vanish_of_expanding_pullback A.abelian.scheme.hom
    (A.abelian.multiplication N).left (A.abelian.multiplication N).w A.graphBundle
    A.graphBundle_isAmple_overAlgClosed hd
    (A.graphBundle_multiplication_iso N).some
    (fun L => A.abelian.fullLevel_multiplication_lineBundleUnit_splitMono A.level hunit L) m hm q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
