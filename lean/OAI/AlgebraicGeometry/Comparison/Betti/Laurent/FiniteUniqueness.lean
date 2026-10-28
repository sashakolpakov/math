import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectorTo
import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectorSum

/-! # Finite Uniqueness -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Laurent.FiniteUniqueness.Dolbeault

noncomputable section

section

/-! Uniqueness of the finite decomposition into normalized Laurent sectors. -/

open _root_.TopologicalSpace Set
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem finiteLaurentSectors_zero (s : Finset ι) (A : Finset ι → (ι → ℂ) → ℂ)
    (hA : ∀ J ∈ s.powerset, Differentiable ℂ (A J))
    (hz : ∀ J ∈ s.powerset, ∀ j ∈ J, ∀ x : ι → ℂ, x j = 0 → A J x = 0)
    (h : ∀ x ∈ SectorTo.Dolbeault.laurentCoordinateDomain s, SectorSum.Dolbeault.laurentSectorSum s A x = 0) :
    ∀ J ∈ s.powerset, A J = 0 := by
  induction s using Finset.induction_on generalizing A with
  | empty =>
    intro J hJ
    have hJe : J = ∅ := by simpa using hJ
    subst J
    funext x
    have hx : x ∈ SectorTo.Dolbeault.laurentCoordinateDomain (∅ : Finset ι) := by
      rw [SectorTo.Dolbeault.laurentCoordinateDomain_empty]
      trivial
    have hinv : SectorTo.Dolbeault.laurentInverseCoordinates (∅ : Finset ι) x = x := by
      funext i
      simp [SectorTo.Dolbeault.laurentInverseCoordinates]
    simpa only [SectorSum.Dolbeault.laurentSectorSum, Finset.powerset_empty, Finset.sum_singleton, hinv,
      Pi.zero_apply] using h x hx
  | @insert i s hi ih =>
    let B : Finset ι → (ι → ℂ) → ℂ := fun J => A (insert i J)
    have hsub (J : Finset ι) (hJ : J ∈ s.powerset) : J ∈ (insert i s).powerset :=
      Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hJ).trans (Finset.subset_insert i s))
    have hins (J : Finset ι) (hJ : J ∈ s.powerset) : insert i J ∈ (insert i s).powerset :=
      Finset.mem_powerset.mpr (Finset.insert_subset_insert i (Finset.mem_powerset.mp hJ))
    have hAs : ∀ J ∈ s.powerset, Differentiable ℂ (A J) := fun J hJ => hA J (hsub J hJ)
    have hBs : ∀ J ∈ s.powerset, Differentiable ℂ (B J) := fun J hJ => hA _ (hins J hJ)
    have hb0 : ∀ x ∈ SectorTo.Dolbeault.laurentCoordinateDomain s, x i = 0 → SectorSum.Dolbeault.laurentSectorSum s B x = 0 := by
      intro x _ hxi
      exact SectorSum.Dolbeault.laurentSectorSum_vanishes s i hi B
        (fun J hJ y hy => hz _ (hins J hJ) i (Finset.mem_insert_self _ _) y hy) x hxi
    have hpair : ∀ x ∈ SectorTo.Dolbeault.laurentCoordinateDomain s,
        SectorSum.Dolbeault.laurentSectorSum s A x = 0 ∧ SectorSum.Dolbeault.laurentSectorSum s B x = 0 := by
      apply SectorTo.Dolbeault.laurentDomain_pair_zero s i hi
        (SectorSum.Dolbeault.laurentSectorSum_differentiableOn s A hAs)
        (SectorSum.Dolbeault.laurentSectorSum_differentiableOn s B hBs) hb0
      intro x hx
      exact (SectorSum.Dolbeault.laurentSectorSum_insert s i hi A x).symm.trans (h x hx)
    have hpos := ih A hAs (fun J hJ j hj x hx => hz J (hsub J hJ) j hj x hx)
      (fun x hx => (hpair x hx).1)
    have hneg := ih B hBs
      (fun J hJ j hj x hx => hz _ (hins J hJ) j (Finset.mem_insert_of_mem hj) x hx)
      (fun x hx => (hpair x hx).2)
    intro J hJ
    have hJs : J ⊆ insert i s := Finset.mem_powerset.mp hJ
    by_cases hiJ : i ∈ J
    · have herase : J.erase i ⊆ s := by
        intro j hj
        rcases Finset.mem_erase.mp hj with ⟨hji, hjJ⟩
        exact (Finset.mem_insert.mp (hJs hjJ)).resolve_left hji
      simpa only [B, Finset.insert_erase hiJ] using hneg (J.erase i) (Finset.mem_powerset.mpr herase)
    · apply hpos J (Finset.mem_powerset.mpr ?_)
      intro j hj
      rcases Finset.mem_insert.mp (hJs hj) with hji | hj
      · exact False.elim (hiJ (hji ▸ hj))
      · exact hj

theorem finiteLaurentSectors_unique (s : Finset ι) (A B : Finset ι → (ι → ℂ) → ℂ)
    (hA : ∀ J ∈ s.powerset, Differentiable ℂ (A J))
    (hB : ∀ J ∈ s.powerset, Differentiable ℂ (B J))
    (hzA : ∀ J ∈ s.powerset, ∀ j ∈ J, ∀ x : ι → ℂ, x j = 0 → A J x = 0)
    (hzB : ∀ J ∈ s.powerset, ∀ j ∈ J, ∀ x : ι → ℂ, x j = 0 → B J x = 0)
    (h : ∀ x ∈ SectorTo.Dolbeault.laurentCoordinateDomain s, SectorSum.Dolbeault.laurentSectorSum s A x = SectorSum.Dolbeault.laurentSectorSum s B x) :
    ∀ J ∈ s.powerset, A J = B J := by
  have hd : ∀ x ∈ SectorTo.Dolbeault.laurentCoordinateDomain s,
      SectorSum.Dolbeault.laurentSectorSum s (fun J x => A J x - B J x) x = 0 := by
    intro x hx
    change (∑ J ∈ s.powerset, (A J (SectorTo.Dolbeault.laurentInverseCoordinates J x) - B J (SectorTo.Dolbeault.laurentInverseCoordinates J x))) = 0
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (h x hx)
  have hz : ∀ J ∈ s.powerset, ∀ j ∈ J, ∀ x : ι → ℂ, x j = 0 → A J x - B J x = 0 := by
    intro J hJ j hj x hx
    rw [hzA J hJ j hj x hx, hzB J hJ j hj x hx, sub_self]
  have he := finiteLaurentSectors_zero s (fun J x => A J x - B J x)
    (fun J hJ => (hA J hJ).sub (hB J hJ)) hz hd
  intro J hJ
  funext x
  exact sub_eq_zero.mp (congrFun (he J hJ) x)

end

/-! Scalar rescaling preserves the unique finite Laurent sectors. -/

open _root_.TopologicalSpace Set
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def laurentUniformScale (c : ℂ) (x : ι → ℂ) : ι → ℂ := fun i => c * x i

def laurentSectorScale (c : ℂ) (J : Finset ι) (x : ι → ℂ) : ι → ℂ :=
  fun i => if i ∈ J then c⁻¹ * x i else c * x i

theorem laurentSectorScale_differentiable (c : ℂ) (J : Finset ι) :
    Differentiable ℂ (laurentSectorScale c J) := by
  apply differentiable_pi.mpr
  intro i
  by_cases hi : i ∈ J
  · simp only [laurentSectorScale, ite_eq_left hi]
    exact (differentiable_apply i).const_mul c⁻¹
  · simp only [laurentSectorScale, ite_eq_right hi]
    exact (differentiable_apply i).const_mul c

omit [Fintype ι] in
theorem laurentInverseCoordinates_scale (c : ℂ) (J : Finset ι) (x : ι → ℂ) :
    SectorTo.Dolbeault.laurentInverseCoordinates J (laurentUniformScale c x) =
      laurentSectorScale c J (SectorTo.Dolbeault.laurentInverseCoordinates J x) := by
  funext i
  by_cases hi : i ∈ J <;> simp [SectorTo.Dolbeault.laurentInverseCoordinates, laurentUniformScale, laurentSectorScale, hi, mul_comm]

theorem laurentUniformScale_mem (s : Finset ι) (c : ℂ) (hc : c ≠ 0)
    (x : ι → ℂ) (hx : x ∈ SectorTo.Dolbeault.laurentCoordinateDomain s) :
    laurentUniformScale c x ∈ SectorTo.Dolbeault.laurentCoordinateDomain s := by
  apply (SectorTo.Dolbeault.mem_laurentCoordinateDomain s _).mpr
  intro i hi
  exact mul_ne_zero hc ((SectorTo.Dolbeault.mem_laurentCoordinateDomain s x).mp hx i hi)

theorem finiteLaurentSectors_scaling (s : Finset ι) (A : Finset ι → (ι → ℂ) → ℂ)
    (hA : ∀ J ∈ s.powerset, Differentiable ℂ (A J))
    (hz : ∀ J ∈ s.powerset, ∀ j ∈ J, ∀ x : ι → ℂ, x j = 0 → A J x = 0)
    (c k : ℂ)
    (h : ∀ x ∈ SectorTo.Dolbeault.laurentCoordinateDomain s,
      SectorSum.Dolbeault.laurentSectorSum s A (laurentUniformScale c x) = k * SectorSum.Dolbeault.laurentSectorSum s A x) :
    ∀ J ∈ s.powerset, ∀ x : ι → ℂ, A J (laurentSectorScale c J x) = k * A J x := by
  have he : ∀ J ∈ s.powerset,
      (fun x => A J (laurentSectorScale c J x)) = (fun x => k * A J x) := by
    apply finiteLaurentSectors_unique s
      (fun J x => A J (laurentSectorScale c J x)) (fun J x => k * A J x)
    · intro J hJ
      exact (hA J hJ).comp (laurentSectorScale_differentiable c J)
    · intro J hJ
      exact (hA J hJ).const_mul k
    · intro J hJ j hj x hx
      apply hz J hJ j hj
      simp only [laurentSectorScale, ite_eq_left hj, hx, mul_zero]
    · intro J hJ j hj x hx
      rw [hz J hJ j hj x hx, mul_zero]
    · intro x hx
      calc
        SectorSum.Dolbeault.laurentSectorSum s (fun J x => A J (laurentSectorScale c J x)) x =
            SectorSum.Dolbeault.laurentSectorSum s A (laurentUniformScale c x) := by
          apply Finset.sum_congr rfl
          intro J _
          rw [laurentInverseCoordinates_scale]
        _ = k * SectorSum.Dolbeault.laurentSectorSum s A x := h x hx
        _ = SectorSum.Dolbeault.laurentSectorSum s (fun J x => k * A J x) x := Finset.mul_sum s.powerset _ k
  intro J hJ x
  exact congrFun (he J hJ) x

end

end OAI.AlgebraicGeometry.Comparison.Betti.Laurent.FiniteUniqueness.Dolbeault
