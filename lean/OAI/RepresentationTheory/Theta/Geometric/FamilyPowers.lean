import OAI.RepresentationTheory.Theta.Geometric.ConsecutiveEmbeddings

/-! # Family Powers -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Powers and enlargements of actual theta families. The powers retain
the original embedding and tangent separation, and contain the pure powers
of every original section. -/

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.redegree {n m : ℕ} (h : n = m) (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n) : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J m where
  toFun := s
  regular := s.regular
  translates l z := by simpa only [h] using s.translates l z

@[simp]
theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.redegree_apply {n m : ℕ} (h : n = m) (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n) (z : Φ.space) :
    s.redegree h z = s z := rfl

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.power (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) : ℕ → AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J
  | 0 => AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.trivial
  | k + 1 => F.mul (F.power k)

@[simp]
theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.power_degree (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (k : ℕ) : (F.power k).degree = F.degree * k := by
  induction k with
  | zero => rfl
  | succ k hk =>
    change F.degree + (F.power k).degree = F.degree * (k + 1)
    rw [hk, Nat.mul_succ, Nat.add_comm]

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.powerSection (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree) :
    (k : ℕ) → AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J (F.power k).degree
  | 0 => AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.one
  | k + 1 => s.mul (F.powerSection s k)

@[simp]
theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.powerSection_apply (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree) (k : ℕ) (z : Φ.space) :
    F.powerSection s k z = s z ^ k := by
  induction k with
  | zero => rfl
  | succ k hk => change s z * F.powerSection s k z = s z ^ (k + 1); rw [hk, pow_succ']

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.powerSection_mem (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree) (hs : s ∈ F.sections) (k : ℕ) :
    F.powerSection s k ∈ (F.power k).sections := by
  induction k with
  | zero => exact Finset.mem_singleton_self _
  | succ k hk => exact F.mul_mem (F.power k) s hs _ hk

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.power_injective (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (k : ℕ) (hk : 0 < k)
    (hF : Function.Injective F.projectiveMap) : Function.Injective (F.power k).projectiveMap := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  exact F.mul_injective (F.power k) hF

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.power_detects (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (k : ℕ) (hk : 0 < k) (p v : Φ.space)
    (hF : F.Detects p v) : (F.power k).Detects p v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  exact F.detects_mul_left (F.power k) p v hF

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.extend (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (S : Finset (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree)) : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J := by
  classical
  exact
    { degree := F.degree
      sections := F.sections ∪ S
      nonzero := fun p => by
        obtain ⟨s, hs, hsp⟩ := F.nonzero p
        exact ⟨s, Finset.mem_union_left _ hs, hsp⟩ }

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.mem_extend_left (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (S : Finset (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree))
    (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree) (hs : s ∈ F.sections) : s ∈ (F.extend S).sections := by
  classical
  exact Finset.mem_union_left _ hs

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.mem_extend_right (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (S : Finset (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree))
    (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree) (hs : s ∈ S) : s ∈ (F.extend S).sections := by
  classical
  exact Finset.mem_union_right _ hs

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.extend_detects (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (S : Finset (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree)) (p v : Φ.space)
    (hF : F.Detects p v) : (F.extend S).Detects p v := by
  obtain ⟨s, hs, t, ht, hsp, hst⟩ := hF
  exact ⟨s, F.mem_extend_left S s hs, t, F.mem_extend_left S t ht, hsp, hst⟩

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.extend_injective (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (S : Finset (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree))
    (hF : Function.Injective F.projectiveMap) : Function.Injective (F.extend S).projectiveMap := by
  intro p q hpq
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective p
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective q
  apply hF
  apply (F.projectiveMap_eq_of_not_separates v w).mpr
  rintro ⟨s, hs, t, ht, hst⟩
  exact ((F.extend S).projectiveMap_eq_of_not_separates v w).mp hpq
    ⟨s, F.mem_extend_left S s hs, t, F.mem_extend_left S t ht, hst⟩

end

end OAI.RepresentationTheory.Theta.Geometric
