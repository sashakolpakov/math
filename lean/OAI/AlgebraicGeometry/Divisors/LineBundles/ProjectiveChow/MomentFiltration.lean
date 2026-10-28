import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.MomentClosed
import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.Filtration

/-! # Moment Filtration -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.MomentFiltration.BundleCycles

noncomputable section

/-! The proper intersection tests are triangular on the actual
projective Chow filtration and detect every class in that filtration. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [E.IsSeparated] [X.IsSeparated] (p : E ⟶ X) [IsProper p] [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E)
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r)

theorem projectiveChowMoment_filtration_zero (d s n bound : ℕ) (h : d = s + n)
    (hb : d + bound ≤ s + r) (α : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d)
    (hα : α ∈ Filtration.BundleCycles.projectiveChowFiltration p f r hp L d bound) : MomentClosed.BundleCycles.projectiveChowMoment p f L d s n h α = 0 := by
  induction hα using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨k, i, hi, hd, β, rfl⟩ := ha
    exact MomentClosed.BundleCycles.projectiveChowMoment_component_zero p f L r hp d s n k i h hd (by omega) β
  | zero => exact map_zero _
  | add a b ha hb ia ib => rw [map_add, ia, ib, add_zero]
  | smul c a ha ia => rw [map_smul, ia, smul_zero]

theorem projectiveChowFiltration_joint_zero (H : Free.ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts p L)
    (d bound : ℕ) (hb : bound ≤ r + 1) (α : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d)
    (hα : α ∈ Filtration.BundleCycles.projectiveChowFiltration p f r hp L d bound)
    (hz : ∀ (s n : ℕ) (h : d = s + n), n ≤ r → MomentClosed.BundleCycles.projectiveChowMoment p f L d s n h α = 0) : α = 0 := by
  induction bound generalizing α with
  | zero =>
    rw [Filtration.BundleCycles.projectiveChowFiltration_zero] at hα
    exact hα
  | succ m ih =>
    by_cases hd : d + m < r
    · rw [Filtration.BundleCycles.projectiveChowFiltration_below_rank p f r hp L d m hd] at hα
      exact hα
    · let k := d + m - r
      have hk : k + r = d + m := by dsimp [k]; omega
      have hn : d = k + (r - m) := by dsimp [k]; omega
      have hm : (r - m) + m = r := by omega
      obtain ⟨γ, hγ, β, he⟩ := Filtration.BundleCycles.projectiveChowFiltration_split p f r hp L d m k hk α hα
      have Hα := hz k (r - m) hn (Nat.sub_le r m)
      have Hγ := projectiveChowMoment_filtration_zero p f L r hp d k (r - m) m hn (by omega) γ hγ
      rw [he, map_add, Hγ, zero_add,
        MomentClosed.BundleCycles.projectiveChowMoment_component_top p f L r hp H d k (r - m) m hn hk hm] at Hα
      have hβ : β = 0 := (smul_eq_zero.mp Hα).resolve_left (pow_ne_zero r (by norm_num))
      have hαγ : α = γ := by simpa only [hβ, map_zero, add_zero] using he
      apply hαγ.trans
      exact ih (by omega) γ hγ (fun s n h hnr => by rw [← hαγ]; exact hz s n h hnr)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.MomentFiltration.BundleCycles
