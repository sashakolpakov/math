import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Card

/-! # Square -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Square.ProjectiveCech

noncomputable section

/-! The actual module Čech differential squares to zero. -/

open _root_.MvPolynomial

universe u v w

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]

def moduleCechValue (f : Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) (s t : Finset σ) (h : t ⊆ s) :
    Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M s := Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M h (f t)

theorem moduleCechValue_congr (f : Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) (s t z : Finset σ)
    (ht : t ⊆ s) (hz : z ⊆ s) (h : t = z) :
    moduleCechValue R M f s t ht = moduleCechValue R M f s z hz := by
  subst z
  rfl

theorem moduleCechDifferential_square (f : Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) :
    Card.ProjectiveCech.moduleCechDifferential R M (Card.ProjectiveCech.moduleCechDifferential R M f) = 0 := by
  funext s
  let F : σ × σ → Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M s := fun p => if p.1 = p.2 then 0 else
    (Cech.Signs.ProjectiveCech.alternatingSign R s p.1 * Cech.Signs.ProjectiveCech.alternatingSign R (s.erase p.1) p.2) •
      moduleCechValue R M f s ((s.erase p.1).erase p.2)
        ((Finset.erase_subset p.2 (s.erase p.1)).trans (Finset.erase_subset p.1 s))
  have hsum : Card.ProjectiveCech.moduleCechDifferential R M (Card.ProjectiveCech.moduleCechDifferential R M f) s =
      ∑ p ∈ s ×ˢ s, F p := by
    change (∑ i ∈ s, Cech.Signs.ProjectiveCech.alternatingSign R s i • Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.erase_subset i s)
      (Card.ProjectiveCech.moduleCechDifferential R M f (s.erase i))) = _
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i _
    change Cech.Signs.ProjectiveCech.alternatingSign R s i • Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.erase_subset i s)
      (∑ j ∈ s.erase i, Cech.Signs.ProjectiveCech.alternatingSign R (s.erase i) j •
        Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.erase_subset j (s.erase i)) (f ((s.erase i).erase j))) = _
    rw [map_sum, Finset.smul_sum]
    simp only [map_smul, smul_smul]
    calc
      _ = ∑ j ∈ s.erase i, F (i, j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hij := (Finset.mem_erase.mp hj).1.symm
        simp only [F, ite_eq_right hij]
        apply congrArg (fun x => (Cech.Signs.ProjectiveCech.alternatingSign R s i * Cech.Signs.ProjectiveCech.alternatingSign R (s.erase i) j) • x)
        exact LinearMap.congr_fun (Presentations.Module.ChartCompatibility.ProjectiveCech.moduleChartRestriction_comp R M
          (Finset.erase_subset j (s.erase i)) (Finset.erase_subset i s)) (f ((s.erase i).erase j))
      _ = ∑ j ∈ s, F (i, j) := by
        apply Finset.sum_subset (Finset.erase_subset i s)
        intro j hj hji
        have hij : i = j := by
          by_contra h
          exact hji (Finset.mem_erase.mpr ⟨Ne.symm h, hj⟩)
        simp only [F, ite_eq_left hij]
  rw [hsum]
  apply Finset.sum_involution (s := s ×ˢ s) (f := F) (fun p _ => p.swap)
  · intro p hp
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hp
    by_cases hij : p.1 = p.2
    · simp only [F, ite_eq_left hij, Prod.fst_swap, Prod.snd_swap, ite_eq_left hij.symm, add_zero]
    · have he : (s.erase p.1).erase p.2 = (s.erase p.2).erase p.1 := by
        ext i
        simp only [Finset.mem_erase]
        tauto
      have hv := moduleCechValue_congr R M f s _ _
        ((Finset.erase_subset p.2 (s.erase p.1)).trans (Finset.erase_subset p.1 s))
        ((Finset.erase_subset p.1 (s.erase p.2)).trans (Finset.erase_subset p.2 s)) he
      simp only [F, ite_eq_right hij, Prod.fst_swap, Prod.snd_swap, ite_eq_right (Ne.symm hij)]
      rw [Cech.Signs.ProjectiveCech.alternatingSign_erase_anticommute R hi hj hij, hv, neg_smul, neg_add_cancel]
  · intro p _ hp hswap
    have hij : p.1 = p.2 := (congrArg Prod.fst hswap).symm
    exact hp (by simp only [F, ite_eq_left hij])
  · intro p hp
    rw [Finset.mem_product]
    exact (Finset.mem_product.mp hp).symm
  · intro p _
    exact Prod.swap_swap p

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Square.ProjectiveCech
