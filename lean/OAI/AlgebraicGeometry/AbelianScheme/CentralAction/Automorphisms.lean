import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Composition

/-! # Automorphisms -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Automorphisms.Construction

noncomputable section

/-! Integral central correspondences are actual automorphisms. Their
complementary exponents multiply to a power of the q-marking shift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def natCentralType {s : ℕ} (a : Fin s → ℕ) (h : ℕ) (ha : ∀ v, a v ≤ h) : TateComparison.Local.IntegralType s :=
  ⟨CentralRepresentatives.Construction.centralType (fun v => a v) h, by
    refine ⟨Int.natCast_nonneg h, ?_⟩
    intro v i
    exact ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr (ha v)⟩⟩

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hgeometry : D.HasIntegralModelGeometry) (hgood : D.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : Interface.Construction.ActionData D)
  (hTateComparison : Interface.Construction.Conclusion D hgeometry hgood hIsogenyQuotient A)

def natCentralMap (a : Fin s → ℕ) (h : ℕ) (ha : ∀ v, a v ≤ h) : End D.space :=
  PEL.Construction.centralModuliMap D hgeometry hIsogenyQuotient hTateComparison.flags (natCentralType a h ha) (fun v => a v)
    (fun _ _ => rfl)

theorem natCentralMap_comp (a b : Fin s → ℕ) (h k : ℕ)
    (ha : ∀ v, a v ≤ h) (hb : ∀ v, b v ≤ k) :
    natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison a h ha ≫
      natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison b k hb =
    natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison (fun v => a v + b v) (h + k)
      (fun v => Nat.add_le_add (ha v) (hb v)) := by
  have hw : (natCentralType (fun v => a v + b v) (h + k)
      (fun v => Nat.add_le_add (ha v) (hb v))).val =
      CentralRepresentatives.Construction.centralType (fun v => (a v : ℤ) + b v) ((h : ℤ) + k) := by
    simp only [natCentralType, Nat.cast_add]
  exact Composition.Construction.centralModuliMap_comp D hgeometry hgood hIsogenyQuotient A hTateComparison
    (natCentralType a h ha) (natCentralType b k hb)
    (natCentralType (fun v => a v + b v) (h + k) (fun v => Nat.add_le_add (ha v) (hb v)))
    (fun v => a v) (fun v => b v) h k rfl rfl hw

theorem natCentralMap_scalar :
    natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison (fun _ => 1) 2 (by intro; omega) =
      A.markingShift.hom := by
  obtain ⟨_, he⟩ := Interface.Construction.correspondenceMap_of_graph
    (D.correspondence (TateComparison.Local.IntegralType.central s)) A.markingShift hTateComparison.scalarGraph
  exact he

theorem natCentralMap_zero :
    natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison (fun _ => 0) 0 (fun _ => le_rfl) =
      𝟙 D.space := by
  have hc := natCentralMap_comp D hgeometry hgood hIsogenyQuotient A hTateComparison
    (fun _ => 1) (fun _ => 0) 2 0 (by intro; omega) (fun _ => le_rfl)
  simp only [Nat.add_zero] at hc
  rw [natCentralMap_scalar] at hc
  apply (cancel_epi A.markingShift.hom).mp
  simpa only [Category.comp_id] using hc

/-- Iteration of an actual central automorphism is the correspondence
whose chosen and opposite exponents have all been multiplied by n. -/
theorem natCentralMap_pow (a : Fin s → ℕ) (h : ℕ) (ha : ∀ v, a v ≤ h) (n : ℕ) :
    natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison a h ha ^ n =
      natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison (fun v => a v * n) (h * n)
        (fun v => Nat.mul_le_mul_right n (ha v)) := by
  induction n with
  | zero =>
    simp only [pow_zero, Nat.mul_zero]
    exact (natCentralMap_zero D hgeometry hgood hIsogenyQuotient A hTateComparison).symm
  | succ n ih =>
    rw [pow_succ', End.mul_def, ih]
    have hc := natCentralMap_comp D hgeometry hgood hIsogenyQuotient A hTateComparison
      (fun v => a v * n) a (h * n) h (fun v => Nat.mul_le_mul_right n (ha v)) ha
    simpa only [Nat.mul_add, Nat.mul_one] using hc

theorem natCentralMap_scalar_pow (n : ℕ) :
    natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison (fun _ => n) (2 * n) (by intro; omega) =
      End.of A.markingShift.hom ^ n := by
  induction n with
  | zero => exact natCentralMap_zero D hgeometry hgood hIsogenyQuotient A hTateComparison
  | succ n ih =>
    have hc := natCentralMap_comp D hgeometry hgood hIsogenyQuotient A hTateComparison
      (fun _ => n) (fun _ => 1) (2 * n) 2 (by intro; omega) (by intro; omega)
    have hr : 2 * n + 2 = 2 * (n + 1) := by omega
    simp only [hr] at hc
    rw [← hc, ih, natCentralMap_scalar, pow_succ', End.mul_def]

/-- Every integral central moduli map is an automorphism on all components. -/
theorem natCentralMap_isIso (a : Fin s → ℕ) (h : ℕ) (ha : ∀ v, a v ≤ h) :
    IsIso (natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison a h ha) := by
  let f : End D.space := natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison a h ha
  let g : End D.space := natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison (fun v => h - a v) h
    (fun v => Nat.sub_le _ _)
  let p : End D.space := natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison (fun _ => h) (2 * h)
    (by intro; omega)
  have hfg : f ≫ g = p := by
    have hc := natCentralMap_comp D hgeometry hgood hIsogenyQuotient A hTateComparison a (fun v => h - a v) h h
      ha (fun v => Nat.sub_le _ _)
    simpa only [Nat.add_sub_of_le (ha _), ← two_mul] using hc
  have hgf : g ≫ f = p := by
    have hc := natCentralMap_comp D hgeometry hgood hIsogenyQuotient A hTateComparison (fun v => h - a v) a h h
      (fun v => Nat.sub_le _ _) ha
    simpa only [Nat.sub_add_cancel (ha _), ← two_mul] using hc
  have hcomm : Commute (f : End D.space) g := by
    change g ≫ f = f ≫ g
    rw [hgf, hfg]
  have hunit : IsUnit (f * g : End D.space) := by
    rw [End.mul_def, hgf]
    change IsUnit (natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison (fun _ => h) (2 * h) _)
    rw [natCentralMap_scalar_pow]
    exact ((isUnit_iff_isIso (End.of A.markingShift.hom)).mpr inferInstance).pow h
  exact (isUnit_iff_isIso f).mp (hcomm.isUnit_mul_iff.mp hunit).1

def natCentralAutomorphism (a : Fin s → ℕ) (h : ℕ) (ha : ∀ v, a v ≤ h) : Aut D.space := by
  have := natCentralMap_isIso D hgeometry hgood hIsogenyQuotient A hTateComparison a h ha
  exact asIso (natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison a h ha)

theorem localType_ext {u v : TateComparison.Local.LocalType s} (hm : u.multiplier = v.multiplier)
    (he : u.exponent = v.exponent) : u = v := by
  cases u
  cases v
  cases hm
  cases he
  rfl

theorem centralModuliMap_isIso (t : TateComparison.Local.IntegralType s) (a : Fin s → ℤ)
    (ha : ∀ v i, t.val.exponent v i = a v) :
    IsIso (PEL.Construction.centralModuliMap D hgeometry hIsogenyQuotient hTateComparison.flags t a ha) := by
  let aN : Fin s → ℕ := fun v => (a v).toNat
  let hN := t.val.multiplier.toNat
  have hnonneg (v : Fin s) : 0 ≤ a v := by
    rw [← ha v 0]
    exact (t.property.2 v 0).1
  have hab : ∀ v, aN v ≤ hN := by
    intro v
    apply Int.toNat_le_toNat
    rw [← ha v 0]
    exact (t.property.2 v 0).2
  have ht : t = natCentralType aN hN hab := by
    apply Subtype.ext
    apply localType_ext
    · exact (Int.toNat_of_nonneg t.property.1).symm
    · funext v i
      rw [ha v i]
      exact (Int.toNat_of_nonneg (hnonneg v)).symm
  have := PEL.Construction.central_correspondence_source_isIso D hgeometry hIsogenyQuotient hTateComparison.flags t a ha
  have hm : PEL.Construction.centralModuliMap D hgeometry hIsogenyQuotient hTateComparison.flags t a ha =
      natCentralMap D hgeometry hgood hIsogenyQuotient A hTateComparison aN hN hab := by
    apply (cancel_epi (D.correspondence t).source).mp
    rw [PEL.Construction.centralModuliMap_source]
    rw [ht]
    exact (PEL.Construction.centralModuliMap_source D hgeometry hIsogenyQuotient hTateComparison.flags (natCentralType aN hN hab)
      (fun v => aN v) (fun _ _ => rfl)).symm
  rw [hm]
  exact natCentralMap_isIso D hgeometry hgood hIsogenyQuotient A hTateComparison aN hN hab

def centralModuliAutomorphism (t : TateComparison.Local.IntegralType s) (a : Fin s → ℤ)
    (ha : ∀ v i, t.val.exponent v i = a v) : Aut D.space := by
  have := centralModuliMap_isIso D hgeometry hgood hIsogenyQuotient A hTateComparison t a ha
  exact asIso (PEL.Construction.centralModuliMap D hgeometry hIsogenyQuotient hTateComparison.flags t a ha)

theorem centralModuliAutomorphism_graph (t : TateComparison.Local.IntegralType s) (a : Fin s → ℤ)
    (ha : ∀ v i, t.val.exponent v i = a v) :
    Interface.Construction.CorrespondenceIsGraph (D.correspondence t)
      (centralModuliAutomorphism D hgeometry hgood hIsogenyQuotient A hTateComparison t a ha) := by
  have := PEL.Construction.central_correspondence_source_isIso D hgeometry hIsogenyQuotient hTateComparison.flags t a ha
  refine ⟨asIso (D.correspondence t).source, rfl, ?_⟩
  exact (PEL.Construction.centralModuliMap_source D hgeometry hIsogenyQuotient hTateComparison.flags t a ha).symm

include hTateComparison in
/-- The two automorphisms in CentralAction's statement are constructed, with the
specified clearing convention for T3 and the unshifted C0 correspondence. -/
theorem exists_central_moduli_automorphisms (active : Fin s) (fullSide : Fin s → Bool) :
    ∃ (σT σC : Aut D.space),
      Interface.Construction.CorrespondenceIsGraph (D.correspondence (CentralRepresentatives.Construction.clearedT3Type active))
        (σT ≪≫ A.markingShift) ∧
      Interface.Construction.CorrespondenceIsGraph (D.correspondence (CentralRepresentatives.Construction.c0IntegralType active fullSide)) σC := by
  let eT := centralModuliAutomorphism D hgeometry hgood hIsogenyQuotient A hTateComparison (CentralRepresentatives.Construction.clearedT3Type active)
    (fun v => CentralRepresentatives.Construction.t3Exponents active v + 1) (fun _ _ => rfl)
  let eC := centralModuliAutomorphism D hgeometry hgood hIsogenyQuotient A hTateComparison
    (CentralRepresentatives.Construction.c0IntegralType active fullSide) (CentralRepresentatives.Construction.c0Exponents active fullSide) (fun _ _ => rfl)
  refine ⟨eT ≪≫ A.markingShift.symm, eC, ?_, ?_⟩
  · have he : (eT ≪≫ A.markingShift.symm) ≪≫ A.markingShift = eT := by
      apply Iso.ext
      change (eT.hom ≫ A.markingShift.inv) ≫ A.markingShift.hom = eT.hom
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [he]
    exact centralModuliAutomorphism_graph D hgeometry hgood hIsogenyQuotient A hTateComparison (CentralRepresentatives.Construction.clearedT3Type active)
      (fun v => CentralRepresentatives.Construction.t3Exponents active v + 1) (fun _ _ => rfl)
  · exact centralModuliAutomorphism_graph D hgeometry hgood hIsogenyQuotient A hTateComparison
      (CentralRepresentatives.Construction.c0IntegralType active fullSide) (CentralRepresentatives.Construction.c0Exponents active fullSide) (fun _ _ => rfl)

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Automorphisms.Construction
