import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Cartan

/-! # Integral Cartan -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralCartan

noncomputable section

section

/-! Integral Cartan bounds come from entrywise integrality of g and
q^h g^-1. They are stable under products and integral changes of basis. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime]

abbrev integralMatrixMonoid := MonoidHom.mrange (CentralConvolution.padicMatrixInclusion q).toMonoidHom

theorem matrix_integral_iff (M : Matrix (Fin 3) (Fin 3) ℚ_[q]) :
    M ∈ integralMatrixMonoid q ↔ ∀ i j, M i j ∈ Set.range (PadicInt.Coe.ringHom (p := q)) := by
  constructor
  · rintro ⟨M, rfl⟩ i j
    exact ⟨M i j, rfl⟩
  · intro h
    choose r hr using h
    exact ⟨r, Matrix.ext (fun i j => hr i j)⟩

theorem q_zpow_integral_iff (a : ℤ) :
    (q : ℚ_[q]) ^ a ∈ Set.range (PadicInt.Coe.ringHom (p := q)) ↔ 0 ≤ a := by
  have hv : ‖(q : ℚ_[q]) ^ a‖ ≤ 1 ↔ 0 ≤ a := by
    rw [Padic.norm_le_one_iff_val_nonneg, Padic.valuation_zpow, Padic.valuation_p, mul_one]
  constructor
  · rintro ⟨r, hr⟩
    apply hv.mp
    rw [← hr]
    exact PadicInt.norm_le_one r
  · intro ha
    exact ⟨⟨(q : ℚ_[q]) ^ a, hv.mpr ha⟩, rfl⟩

theorem diagonal_integral_iff (a : Fin 3 → ℤ) :
    (HeckeKernel.diagonalUnit (fun i => HeckeKernel.qUnit q ^ a i)).val ∈ integralMatrixMonoid q ↔
      ∀ i, 0 ≤ a i := by
  rw [matrix_integral_iff]
  have hdiag (i : Fin 3) : (HeckeKernel.diagonalUnit (fun j => HeckeKernel.qUnit q ^ a j)).val i i =
      (q : ℚ_[q]) ^ a i := by
    simp [HeckeKernel.diagonalUnit, HeckeKernel.qUnit]
  constructor
  · intro h i
    exact (q_zpow_integral_iff q (a i)).mp (hdiag i ▸ h i i)
  · intro h i j
    by_cases hij : i = j
    · subst j
      rw [hdiag]
      exact (q_zpow_integral_iff q (a i)).mpr (h i)
    · have hz : (HeckeKernel.diagonalUnit (fun j => HeckeKernel.qUnit q ^ a j)).val i j = 0 := by
        simp [HeckeKernel.diagonalUnit, hij]
      rw [hz]
      exact ⟨0, map_zero _⟩

def IntegralGLBound (h : ℕ) (g : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]) : Prop :=
  g.val ∈ integralMatrixMonoid q ∧
    (Matrix.GeneralLinearGroup.scalar (Fin 3) (HeckeKernel.qUnit q ^ h) * g⁻¹).val ∈ integralMatrixMonoid q

theorem integralGLBound_of_level {g : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]}
    (hg : g ∈ (Matrix.GeneralLinearGroup.map (n := Fin 3)
      (PadicInt.Coe.ringHom (p := q))).range) : IntegralGLBound q 0 g := by
  change g ∈ (Units.map (CentralConvolution.padicMatrixInclusion q).toMonoidHom).range at hg
  rw [CentralConvolution.unitsMap_range _ (CentralConvolution.padicMatrixInclusion_isOpenEmbedding q).injective] at hg
  change g.val ∈ integralMatrixMonoid q ∧ g⁻¹.val ∈ integralMatrixMonoid q at hg
  refine ⟨hg.1, ?_⟩
  simpa only [pow_zero, map_one, one_mul] using hg.2

theorem integralGLBound_mul {h k : ℕ} {g f : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]}
    (hg : IntegralGLBound q h g) (hf : IntegralGLBound q k f) :
    IntegralGLBound q (h + k) (g * f) := by
  refine ⟨(integralMatrixMonoid q).mul_mem hg.1 hf.1, ?_⟩
  have heq : Matrix.GeneralLinearGroup.scalar (Fin 3) (HeckeKernel.qUnit q ^ (h + k)) * (g * f)⁻¹ =
      (Matrix.GeneralLinearGroup.scalar (Fin 3) (HeckeKernel.qUnit q ^ k) * f⁻¹) *
        (Matrix.GeneralLinearGroup.scalar (Fin 3) (HeckeKernel.qUnit q ^ h) * g⁻¹) := by
    rw [pow_add, map_mul, mul_inv_rev]
    calc
      _ = (Matrix.GeneralLinearGroup.scalar (Fin 3) (HeckeKernel.qUnit q ^ h) *
          (Matrix.GeneralLinearGroup.scalar (Fin 3) (HeckeKernel.qUnit q ^ k) * f⁻¹)) * g⁻¹ := by
        simp only [mul_assoc]
      _ = ((Matrix.GeneralLinearGroup.scalar (Fin 3) (HeckeKernel.qUnit q ^ k) * f⁻¹) *
          Matrix.GeneralLinearGroup.scalar (Fin 3) (HeckeKernel.qUnit q ^ h)) * g⁻¹ := by
        rw [Matrix.GeneralLinearGroup.scalar_commute]
      _ = _ := mul_assoc _ _ _
  rw [heq]
  exact (integralMatrixMonoid q).mul_mem hf.2 hg.2

theorem scalar_inverse_diagonal (h : ℕ) (a : Fin 3 → ℤ) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) (HeckeKernel.qUnit q ^ h) *
      (HeckeKernel.diagonalUnit (fun i => HeckeKernel.qUnit q ^ a i))⁻¹ =
        HeckeKernel.diagonalUnit (fun i => HeckeKernel.qUnit q ^ ((h : ℤ) - a i)) := by
  have hs : Matrix.GeneralLinearGroup.scalar (Fin 3) (HeckeKernel.qUnit q ^ h) =
      CentralConvolution.diagonalHom (fun _ => HeckeKernel.qUnit q ^ h) := by
    apply Units.ext
    rfl
  rw [hs]
  change CentralConvolution.diagonalHom _ * (CentralConvolution.diagonalHom _)⁻¹ = CentralConvolution.diagonalHom _
  rw [← map_inv, ← map_mul]
  congr 1
  funext i
  simp only [Pi.mul_apply, Pi.inv_apply, sub_eq_add_neg, zpow_add, zpow_neg, zpow_natCast]

theorem integralGLBound_diagonal_iff (h : ℕ) (a : Fin 3 → ℤ) :
    IntegralGLBound q h (HeckeKernel.diagonalUnit (fun i => HeckeKernel.qUnit q ^ a i)) ↔
      ∀ i, 0 ≤ a i ∧ a i ≤ (h : ℤ) := by
  unfold IntegralGLBound
  rw [diagonal_integral_iff, scalar_inverse_diagonal, diagonal_integral_iff]
  constructor
  · rintro ⟨hl, hu⟩ i
    exact ⟨hl i, sub_nonneg.mp (hu i)⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => sub_nonneg.mpr (h i).2⟩

/-- Applying integral inverse basis changes reduces the bounds to the
diagonal. Thus ElementaryDivisors's Cartan exponents lie in the prescribed interval. -/
theorem exists_integral_GL3_cartan (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (h : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]) (hg : IntegralGLBound q h g) :
    ∃ a : Fin 3 → ℤ, Antitone a ∧ (∀ i, 0 ≤ a i ∧ a i ≤ (h : ℤ)) ∧
      ∃ l r : Matrix.GeneralLinearGroup (Fin 3) ℤ_[q],
        g = Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) l *
          HeckeKernel.diagonalUnit (fun i => HeckeKernel.qUnit q ^ a i) *
          Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := q)) r := by
  obtain ⟨a, ha, l, r, hgr⟩ := Cartan.exists_GL3_cartan q hElementaryDivisors g
  let F := Matrix.GeneralLinearGroup.map (n := Fin 3) (PadicInt.Coe.ringHom (p := q))
  have hl : IntegralGLBound q 0 (F l)⁻¹ :=
    integralGLBound_of_level q (F.range.inv_mem ⟨l, rfl⟩)
  have hr : IntegralGLBound q 0 (F r)⁻¹ :=
    integralGLBound_of_level q (F.range.inv_mem ⟨r, rfl⟩)
  have hb := integralGLBound_mul q (integralGLBound_mul q hl hg) hr
  have heq : (F l)⁻¹ * g * (F r)⁻¹ = HeckeKernel.diagonalUnit (fun i => HeckeKernel.qUnit q ^ a i) := by
    rw [hgr]
    change (F l)⁻¹ * (F l * _ * F r) * (F r)⁻¹ = _
    group
  rw [heq, zero_add, add_zero] at hb
  exact ⟨a, ha, (integralGLBound_diagonal_iff q h a).mp hb, l, r, hgr⟩

end

/-! Integral split-group elements form a monoid. ElementaryDivisors puts every such
element in a double coset in the precise IsogenyQuotient integral range. -/

open scoped Classical

variable (s q : ℕ) [Fact q.Prime]

def IntegralSplitBound (h : ℕ) (g : HeckeKernel.SplitGroup s q) : Prop :=
  (∃ u : ℤ_[q]ˣ, g.2 =
    Units.map (PadicInt.Coe.ringHom (p := q)).toMonoidHom u * HeckeKernel.qUnit q ^ h) ∧
  ∀ v, IntegralGLBound q h (g.1 v)

theorem integralSplitBound_of_level {g : HeckeKernel.SplitGroup s q} (hg : g ∈ HeckeKernel.integralLevel s q) :
    IntegralSplitBound s q 0 g := by
  obtain ⟨hm, u, hu⟩ := (CentralConvolution.integralLevel_mem_iff s q g).mp hg
  refine ⟨⟨u, ?_⟩, fun v => integralGLBound_of_level q (hm v)⟩
  simpa only [pow_zero, mul_one] using hu.symm

theorem integralSplitBound_mul {h k : ℕ} {g f : HeckeKernel.SplitGroup s q}
    (hg : IntegralSplitBound s q h g) (hf : IntegralSplitBound s q k f) :
    IntegralSplitBound s q (h + k) (g * f) := by
  obtain ⟨⟨u, hu⟩, hgm⟩ := hg
  obtain ⟨⟨v, hv⟩, hfm⟩ := hf
  refine ⟨⟨u * v, ?_⟩, fun w => integralGLBound_mul q (hgm w) (hfm w)⟩
  change g.2 * f.2 = _
  rw [hu, hv, map_mul, pow_add]
  ac_rfl

theorem integralSplitBound_representative (t : Local.IntegralType s) :
    IntegralSplitBound s q t.val.multiplier.toNat (HeckeKernel.representative s q t.val) := by
  have hh : (t.val.multiplier.toNat : ℤ) = t.val.multiplier :=
    Int.toNat_of_nonneg t.property.1
  refine ⟨⟨1, ?_⟩, ?_⟩
  · change HeckeKernel.qUnit q ^ t.val.multiplier = _
    rw [map_one, one_mul, ← zpow_natCast, hh]
  · intro v
    apply (integralGLBound_diagonal_iff q _ _).mpr
    intro i
    rw [hh]
    exact t.property.2 v i

def integralSplitMonoid : Submonoid (HeckeKernel.SplitGroup s q) where
  carrier := {g | ∃ h : ℕ, IntegralSplitBound s q h g}
  one_mem' := ⟨0, integralSplitBound_of_level s q (HeckeKernel.integralLevel s q).one_mem⟩
  mul_mem' := by
    rintro g f ⟨h, hg⟩ ⟨k, hf⟩
    exact ⟨h + k, integralSplitBound_mul s q hg hf⟩

theorem level_mem_integralSplitMonoid {g : HeckeKernel.SplitGroup s q} (hg : g ∈ HeckeKernel.integralLevel s q) :
    g ∈ integralSplitMonoid s q := ⟨0, integralSplitBound_of_level s q hg⟩

theorem representative_mem_integralSplitMonoid (t : Local.IntegralType s) :
    HeckeKernel.representative s q t.val ∈ integralSplitMonoid s q :=
  ⟨t.val.multiplier.toNat, integralSplitBound_representative s q t⟩

theorem exists_integral_split_cartan (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (g : HeckeKernel.SplitGroup s q) (hg : g ∈ integralSplitMonoid s q) :
    ∃ t : Local.IntegralType s, ∃ l r : HeckeKernel.integralLevel s q,
      g = (l : HeckeKernel.SplitGroup s q) * HeckeKernel.representative s q t.val * (r : HeckeKernel.SplitGroup s q) := by
  obtain ⟨h, ⟨u, hu⟩, hb⟩ := hg
  choose a ha using fun v => exists_integral_GL3_cartan q hElementaryDivisors h (g.1 v) (hb v)
  choose l r hlr using fun v => (ha v).2.2
  let t : Local.IntegralType s :=
    ⟨⟨h, a, fun v => (ha v).1⟩, Int.natCast_nonneg h, fun v i => (ha v).2.1 i⟩
  let l' : HeckeKernel.integralLevel s q := ⟨HeckeKernel.integralLevelMap s q (l, u), ⟨(l, u), rfl⟩⟩
  let r' : HeckeKernel.integralLevel s q := ⟨HeckeKernel.integralLevelMap s q (r, 1), ⟨(r, 1), rfl⟩⟩
  refine ⟨t, l', r', Prod.ext ?_ ?_⟩
  · funext v
    exact hlr v
  · change g.2 = (Units.map (PadicInt.Coe.ringHom (p := q)).toMonoidHom u *
      HeckeKernel.qUnit q ^ (h : ℤ)) * Units.map (PadicInt.Coe.ringHom (p := q)).toMonoidHom 1
    rw [map_one, mul_one, zpow_natCast]
    exact hu

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralCartan
