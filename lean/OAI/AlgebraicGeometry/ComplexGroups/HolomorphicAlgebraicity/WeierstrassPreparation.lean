import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Moments
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SymmetricRootsOn

/-! # Weierstrass Preparation -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.WeierstrassPreparation.Constructions.Preparation

noncomputable section

/-!
# Local polynomial preparation of a holomorphic family

A fiber with no boundary zeros supplies a neighborhood on which its enclosed
zeros are represented by a monic polynomial of fixed degree and holomorphic
coefficients. The construction retains multiplicities and yields the actual
factorization of each fiber by an analytic nonvanishing function.
-/

open Set Filter _root_.Metric _root_.Complex _root_.Polynomial
open scoped _root_.Topology BigOperators

theorem exists_polynomial_preparation {n : ℕ} {F : (Fin n → ℂ) × ℂ → ℂ}
    {W : Set ((Fin n → ℂ) × ℂ)} (hW : IsOpen W)
    (hF : DifferentiableOn ℂ F W) {x : Fin n → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hbase : ∀ z ∈ closedBall c R, (x, z) ∈ W)
    (hn : ∀ z ∈ sphere c R, F (x, z) ≠ 0) :
    ∃ (d : ℕ) (U : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → Polynomial ℂ),
      IsOpen U ∧ x ∈ U ∧ U ×ˢ closedBall c R ⊆ W ∧
      (∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) U) ∧
      ∀ y ∈ U, (P y).Monic ∧ (P y).natDegree = d ∧
        (∀ z, (P y).eval z = 0 → z ∈ ball c R) ∧
        ∃ u : ℂ → ℂ, AnalyticOnNhd ℂ u (closedBall c R) ∧
          (∀ z ∈ closedBall c R, u z ≠ 0) ∧
          ∀ z ∈ closedBall c R, (fun w => F (y, w)) =ᶠ[𝓝 z]
            (fun w => (P y).eval w * u w) := by
  classical
  obtain ⟨d, U, hU, hx, hUW, hUn, hdata⟩ :=
    RootFamiliesAt.Constructions.RootFamilies.exists_fixed_degree_factorization hW hF hR hbase hn
  choose roots unit hr hu hun hfu hm using hdata
  let r : (Fin n → ℂ) → Fin d → ℂ := fun y => if hy : y ∈ U then roots y hy else 0
  have heq (y : Fin n → ℂ) (hy : y ∈ U) : r y = roots y hy := dite_eq_left hy
  let P : (Fin n → ℂ) → Polynomial ℂ := fun y => SymmetricRootsOn.Constructions.SymmetricRoots.rootPolynomial (r y)
  have hpower (k : ℕ) : DifferentiableOn ℂ (fun y => ∑ i, r y i ^ k) U := by
    apply (Moments.Constructions.RootFamilies.differentiableOn_moment hW hF hU hR.le
      (fun p hp => hUW ⟨hp.1, sphere_subset_closedBall hp.2⟩) hUn k).congr
    intro y hy
    rw [heq y hy]
    exact (hm y hy k).symm
  refine ⟨d, U, P, hU, hx, hUW,
    fun k => SymmetricRootsOn.Constructions.SymmetricRoots.differentiableOn_rootPolynomial_coeff r hpower k, ?_⟩
  intro y hy
  have hPeval (z : ℂ) : (P y).eval z = RootMomentsNe.Constructions.RootMoments.rootProduct (roots y hy) z := by
    simp only [P, SymmetricRootsOn.Constructions.SymmetricRoots.rootPolynomial, eval_prod, eval_sub, eval_X, eval_C,
      heq y hy, RootMomentsNe.Constructions.RootMoments.rootProduct]
  refine ⟨SymmetricRootsOn.Constructions.SymmetricRoots.rootPolynomial_monic _, SymmetricRootsOn.Constructions.SymmetricRoots.rootPolynomial_natDegree _,
    ?_, unit y hy, hu y hy, hun y hy, ?_⟩
  · intro z hz
    rw [hPeval, RootMomentsNe.Constructions.RootMoments.rootProduct] at hz
    obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hz
    rw [sub_eq_zero.mp hi]
    exact hr y hy i
  · intro z hz
    simpa only [hPeval] using hfu y hy z hz

/-- The prepared polynomial gives exact equations for the original zero set
on a product neighborhood, with no selected-root regularity assumption. -/
theorem exists_polynomial_zero_equations {n : ℕ} {F : (Fin n → ℂ) × ℂ → ℂ}
    {W : Set ((Fin n → ℂ) × ℂ)} (hW : IsOpen W)
    (hF : DifferentiableOn ℂ F W) {x : Fin n → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hbase : ∀ z ∈ closedBall c R, (x, z) ∈ W)
    (hn : ∀ z ∈ sphere c R, F (x, z) ≠ 0) :
    ∃ (d : ℕ) (U : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → Polynomial ℂ),
      IsOpen U ∧ x ∈ U ∧ U ×ˢ closedBall c R ⊆ W ∧
      (∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) U) ∧
      (∀ y ∈ U, (P y).Monic ∧ (P y).natDegree = d ∧
        ∀ z, (P y).eval z = 0 → z ∈ ball c R) ∧
      ∀ y ∈ U, ∀ z ∈ closedBall c R, F (y, z) = 0 ↔ (P y).eval z = 0 := by
  obtain ⟨d, U, P, hU, hx, hUW, hcoeff, hdata⟩ :=
    exists_polynomial_preparation hW hF hR hbase hn
  refine ⟨d, U, P, hU, hx, hUW, hcoeff,
    fun y hy => ⟨(hdata y hy).1, (hdata y hy).2.1, (hdata y hy).2.2.1⟩, ?_⟩
  intro y hy z hz
  obtain ⟨_, _, _, u, _, hun, hfu⟩ := hdata y hy
  rw [(hfu z hz).eq_of_nhds, mul_eq_zero, or_iff_left (hun z hz)]

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.WeierstrassPreparation.Constructions.Preparation
