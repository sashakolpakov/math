import OAI.Analysis.PDE.Elliptic.CompactOperators
import OAI.Analysis.PDE.Elliptic.SignedFrame
import OAI.Analysis.PDE.Elliptic.FrameCompletion

open InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- Every operator with the prescribed ellipticity bounds has a decomposition
in a single finite collection of fixed directions. All coefficients have
uniform positive lower and upper bounds, chosen before the operator. -/
theorem uniform_signed_frame_decomposition {lam L : ℝ}
    (hlam : 0 < lam) (hL : lam ≤ L) :
    ∃ bs : Finset (OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E),
      bs.Nonempty ∧ ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ A : E →L[ℝ] E, A.toLinearMap.IsSymmetric →
        (∀ x, lam * ‖x‖ ^ 2 ≤ inner ℝ x (A x)) →
        (∀ x, inner ℝ x (A x) ≤ L * ‖x‖ ^ 2) →
        ∃ c : {b // b ∈ bs} → SignedFrameIndex (Fin (Module.finrank ℝ E)) → ℝ,
          (∀ b q, δ ≤ c b q ∧ c b q ≤ C) ∧
          A = ∑ b, ∑ q, c b q •
            rankOne ℝ (signedFrame b.val q) (signedFrame b.val q) := by
  classical
  let I := Fin (Module.finrank ℝ E)
  let n : ℝ := Fintype.card I
  have hn : 0 < n := by
    simp only [n, I, Fintype.card_fin]
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  let eps := lam / (2 * n)
  have heps : 0 < eps := div_pos hlam (by positivity)
  have hsize : eps * Fintype.card I = lam / 2 := by
    change (lam / (2 * n)) * n = lam / 2
    field_simp [ne_of_gt hn]
  have hL0 : 0 ≤ L := le_trans hlam.le hL
  obtain ⟨bs, hbs⟩ := finite_basis_uniform_quadratic (E := E) hL0 (half_pos heps)
  obtain ⟨bzero, hbzero, _⟩ := hbs 0 (by intro x y; simp)
    (by intro x; simp) (by intro x; simpa using mul_nonneg hL0 (sq_nonneg ‖x‖))
  let B := {b // b ∈ bs}
  let : Nonempty B := ⟨⟨bzero, hbzero⟩⟩
  let v : B → SignedFrameIndex I → (E →L[ℝ] E) :=
    fun b q ↦ rankOne ℝ (signedFrame b.val q) (signedFrame b.val q)
  let P := (1 + 4 * n) • ContinuousLinearMap.id ℝ E
  have hframe : ∀ b, ∑ q, v b q = P := fun b ↦ signedFrame_sum b.val
  let m := min (lam / 2) (eps / 8)
  have hm : 0 < m := lt_min (half_pos hlam) (by positivity)
  have hcap : m ≤ L + eps := by
    have h := min_le_right (lam / 2) (eps / 8)
    dsimp [m]
    linarith
  obtain ⟨δ, hδ, hcomplete⟩ := finite_frame_positive_completion v P hframe hm hcap
  refine ⟨bs, ⟨bzero, hbzero⟩, δ, L + eps, hδ, by positivity, ?_⟩
  intro A hA hlo hhi
  obtain ⟨b, hb, hnear⟩ := hbs A hA
    (fun x ↦ le_trans (mul_nonneg hlam.le (sq_nonneg _)) (hlo x)) hhi
  let a : I → I → ℝ := fun i j ↦ inner ℝ (b i) (A (b j))
  have ha : ∀ i j, a i j = a j i := by
    intro i j
    dsimp [a]
    calc
      _ = inner ℝ (A (b i)) (b j) := (hA (b i) (b j)).symm
      _ = _ := real_inner_comm _ _
  have hdiag : ∀ i, lam ≤ a i i ∧ a i i ≤ L := by
    intro i
    constructor
    · simpa [a, b.norm_eq_one] using hlo (b i)
    · simpa [a, b.norm_eq_one] using hhi (b i)
  have hsmall : ∀ i j, |offDiagonal a i j| ≤ eps / 2 := by
    intro i j
    by_cases hij : i = j
    · simpa [offDiagonal, hij] using (half_pos heps).le
    · simpa [offDiagonal, hij, a] using (hnear i j hij).le
  have hcoeff := signedCoefficient_bounds hL0 heps.le hdiag hsmall hsize.le
  obtain ⟨c, hc, hsum⟩ := hcomplete ⟨b, hb⟩ (signedCoefficient a eps) hcoeff
  refine ⟨c, hc, ?_⟩
  have hrep : (∑ q, signedCoefficient a eps q • rankOne ℝ
      (signedFrame b q) (signedFrame b q)) = A :=
    (signedFrame_representation b a ha eps).trans (operator_rankOne_double_basis b A).symm
  exact (hsum.trans hrep).symm

end OAI.Analysis.PDE.Elliptic
