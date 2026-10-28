import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation

/-! # Kernel Quotient -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.KernelQuotient.Tate

noncomputable section

/-! The finite-level kernel is the cokernel on Tate modules when a
q-power reverse map is supplied. This is the exact-sequence calculation
used with the reverse map constructed from a polarization. -/

universe u
variable (q : ℕ) [Fact q.Prime] {H H' : Type u} [AddCommGroup H] [AddCommGroup H']

theorem evaluate_map (f : H →+ H') (n : ℕ) (x : Add.Tate.Module (H := H) q) :
    Evaluation.Tate.evaluate q n (Add.Tate.map q f x) = Add.Tate.mapLevel q f n (Evaluation.Tate.evaluate q n x) := rfl

theorem q_pow_smul_cancel (n : ℕ) {x y : Add.Tate.Module (H := H) q}
    (h : (q : ℤ_[q]) ^ n • x = (q : ℤ_[q]) ^ n • y) : x = y := by
  apply sub_eq_zero.mp
  apply Functor.Tate.q_pow_smul_eq_zero q n (x - y)
  rw [smul_sub, h, sub_self]

variable (f : H →+ H') (n : ℕ)
  (g : Add.Tate.Module (H := H') q →ₗ[ℤ_[q]] Add.Tate.Module (H := H) q)
  (hgf : g.comp (Add.Tate.map q f) = (q : ℤ_[q]) ^ n • LinearMap.id)
  (hfg : (Add.Tate.map q f).comp g = (q : ℤ_[q]) ^ n • LinearMap.id)

def kernelBoundary : Add.Tate.Module (H := H') q →ₗ[ℤ_[q]] (Add.Tate.mapLevel q f n).ker :=
  ((Evaluation.Tate.evaluate q n).comp g).codRestrict (Add.Tate.mapLevel q f n).ker (by
    intro y
    change Add.Tate.mapLevel q f n (Evaluation.Tate.evaluate q n (g y)) = 0
    rw [← evaluate_map]
    have hy := congrArg (fun a => a y) hfg
    change Add.Tate.map q f (g y) = (q : ℤ_[q]) ^ n • y at hy
    rw [hy]
    exact (Evaluation.Tate.evaluate_eq_zero_iff q n _).mpr ⟨y, rfl⟩)

include hgf in
theorem kernelBoundary_ker :
    (kernelBoundary q f n g hfg).ker = (Add.Tate.map q f).range := by
  apply Submodule.ext
  intro y
  constructor
  · intro hy
    have hz : Evaluation.Tate.evaluate q n (g y) = 0 := congrArg Subtype.val hy
    obtain ⟨x, hx⟩ := (Evaluation.Tate.evaluate_eq_zero_iff q n (g y)).mp hz
    refine ⟨x, q_pow_smul_cancel q n ?_⟩
    have he := congrArg (Add.Tate.map q f) hx
    rw [map_smul] at he
    have hy' := congrArg (fun a => a y) hfg
    exact he.trans hy'
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    change Evaluation.Tate.evaluate q n (g (Add.Tate.map q f x)) = 0
    have hx := congrArg (fun a => a x) hgf
    change g (Add.Tate.map q f x) = (q : ℤ_[q]) ^ n • x at hx
    rw [hx]
    exact (Evaluation.Tate.evaluate_eq_zero_iff q n _).mpr ⟨x, rfl⟩

include hgf in
theorem kernelBoundary_surjective (hdiv : ∀ x : H, ∃ y, q • y = x) :
    Function.Surjective (kernelBoundary q f n g hfg) := by
  intro a
  obtain ⟨x, hx⟩ := Evaluation.Tate.evaluate_surjective q hdiv n a.val
  have he : Evaluation.Tate.evaluate q n (Add.Tate.map q f x) = 0 := by
    rw [evaluate_map, hx]
    exact a.property
  obtain ⟨y, hy⟩ := (Evaluation.Tate.evaluate_eq_zero_iff q n (Add.Tate.map q f x)).mp he
  have hxy : g y = x := by
    apply q_pow_smul_cancel q n
    have he := congrArg g hy
    rw [map_smul] at he
    exact he.trans (congrArg (fun z => z x) hgf)
  refine ⟨y, ?_⟩
  apply Subtype.ext
  change Evaluation.Tate.evaluate q n (g y) = a.val
  rw [hxy, hx]

def cokernelEquivKernel (hdiv : ∀ x : H, ∃ y, q • y = x) :
    (Add.Tate.Module (H := H') q ⧸ (Add.Tate.map q f).range) ≃ₗ[ℤ_[q]] (Add.Tate.mapLevel q f n).ker :=
  (Submodule.quotEquivOfEq _ _ (kernelBoundary_ker q f n g hgf hfg).symm).trans
    ((kernelBoundary q f n g hfg).quotKerEquivOfSurjective
      (kernelBoundary_surjective q f n g hgf hfg hdiv))

include hgf in
theorem map_injective_of_reverse : Function.Injective (Add.Tate.map q f) := by
  intro x y hxy
  apply q_pow_smul_cancel q n
  exact (congrArg (fun a => a x) hgf).symm.trans
    ((congrArg g hxy).trans (congrArg (fun a => a y) hgf))

include hgf hfg in
theorem reverse_intertwines (a : Add.Tate.Module (H := H) q →ₗ[ℤ_[q]] Add.Tate.Module (H := H) q)
    (b : Add.Tate.Module (H := H') q →ₗ[ℤ_[q]] Add.Tate.Module (H := H') q)
    (h : (Add.Tate.map q f).comp a = b.comp (Add.Tate.map q f)) : g.comp b = a.comp g := by
  apply LinearMap.ext
  intro y
  apply map_injective_of_reverse q f n g hgf
  change Add.Tate.map q f (g (b y)) = Add.Tate.map q f (a (g y))
  have hy := congrArg (fun z => z y) hfg
  have hby := congrArg (fun z => z (b y)) hfg
  have ha := congrArg (fun z => z (g y)) h
  change Add.Tate.map q f (g y) = (q : ℤ_[q]) ^ n • y at hy
  change Add.Tate.map q f (g (b y)) = (q : ℤ_[q]) ^ n • b y at hby
  change Add.Tate.map q f (a (g y)) = b (Add.Tate.map q f (g y)) at ha
  rw [hby, ha, hy, map_smul]

include hgf hfg in
theorem boundary_raw_ker : ((Evaluation.Tate.evaluate q n).comp g).ker = (Add.Tate.map q f).range := by
  rw [← kernelBoundary_ker q f n g hgf hfg]
  ext y
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg Subtype.val h

include hgf hfg in
theorem boundary_raw_range (hdiv : ∀ x : H, ∃ y, q • y = x) :
    ((Evaluation.Tate.evaluate q n).comp g).range = (Add.Tate.mapLevel q f n).ker := by
  ext a
  constructor
  · rintro ⟨y, rfl⟩
    exact (kernelBoundary q f n g hfg y).property
  · intro ha
    obtain ⟨y, hy⟩ := kernelBoundary_surjective q f n g hgf hfg hdiv ⟨a, ha⟩
    exact ⟨y, congrArg Subtype.val hy⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.KernelQuotient.Tate
