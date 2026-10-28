import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HyperplaneFiberPointBound
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.PowerIntersectionData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.ClosedIntegrality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LevelMultiplication.Finite
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReducedSectionNonvanishing

/-! # Power Torsion Hyperplane Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! For an actual canonical graph-bundle power embedding, the number
of distinct n-torsion points on any nonzero hyperplane section is at
most its Euler coefficient times the dimension factorial times
n^(2g-2). The full level supplies finiteness of multiplication. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundlePower_torsion_hyperplane_card_le
    {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} {δ : Fin (g + 1) → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel (g + 1) δ N (Spec (.of K)))
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) (k : ℕ) {r : ℕ}
    (s : Fin (r + 1) → (Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower k).sheaf))
    (hcover : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ha : ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i)))
    (hgen : Section.ProjectivePresentation.SectionRatiosGenerate A.abelian.scheme.hom s)
    (n : ℕ) (hn : 0 < n) (level : A.abelian.FullLevel n)
    (a : Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower k).sheaf) (ha0 : a ≠ 0)
    {κ : Type v} [Finite κ] (x : κ → A.abelian.scheme.left) (hx : Function.Injective x)
    (hxa : ∀ i, x i ∉ Ample.LineBundles.sectionNonvanishing a)
    (hxn : ∀ i, (A.abelian.multiplication n).left (x i) =
      η[A.abelian.scheme].left (IsLocalRing.closedPoint K)) :
    (Nat.card κ : ℤ) ≤
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom (A.graphBundle.tensorPower k).sheaf *
        ((g + 1).factorial : ℤ) * (n : ℤ) ^ (2 * g) := by
  let : IsIntegral A.abelian.scheme.left := A.abelian.integral_overAlgClosed
  let : IsFinite (A.abelian.multiplication n).left := A.abelian.fullLevel_multiplication_isFinite level
  have ha_nonzero := (A.graphBundle.tensorPower k).exists_nonvanishing_of_ne_zero a ha0
  have h := HyperplaneFiberPointBound.hyperplane_fiber_configuration_card_le A.abelian.scheme.hom g (A.graphBundle.tensorPower k)
    s hcover ha hgen η[A.abelian.scheme].left η[A.abelian.scheme].w
    (A.abelian.multiplication n).left
    (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom (A.graphBundle.tensorPower k).sheaf)
    ((n : ℤ) ^ 2) (pow_ne_zero _ (by exact_mod_cast (Nat.ne_of_gt hn)))
    (A.graphBundlePower_multiplication_class k n) (A.graphBundlePower_integerPower_euler hN hNk k)
    a ha_nonzero x hx hxa hxn
  simpa only [← pow_mul] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
