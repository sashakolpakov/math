import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.TateLattices
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives

/-! # Scalar Tate Lattice -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ScalarTateLattice.Construction

noncomputable section

/-! The marked principal scalar realizes precisely its inverse central
Tate lattice, with the q-adic unit factors removed inside each integral block. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj Pointwise

variable (q : ℕ) [Fact q.Prime]

theorem padic_scalar_lattice_preimage
    (L : Submodule ℤ_[q] (Fin 3 → ℚ_[q])) (a : ℕ) (u : ℤ_[q]ˣ) (x : Fin 3 → ℚ_[q]) :
    ((q : ℚ_[q]) ^ a * (u : ℤ_[q])) • x ∈ L ↔
      x ∈ (TateComparison.HeckeKernel.qUnit q ^ (-(a : ℤ))) • L := by
  rw [mul_comm, mul_smul]
  change (u : ℤ_[q]) • ((q : ℚ_[q]) ^ a • x) ∈ L ↔ _
  rw [L.smul_mem_iff_of_isUnit u.isUnit]
  change (q : ℚ_[q]) ^ a • x ∈ L ↔ x ∈ (TateComparison.HeckeKernel.qUnit q ^ (-(a : ℤ))) • (L : Set (Fin 3 → ℚ_[q]))
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp only [← zpow_neg, neg_neg, zpow_natCast, Units.smul_def, Units.val_pow_eq_pow_val]
  rfl

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  {S : Scheme} {g N s m : ℕ}
  (P : TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S) (T : Over S)

omit [NumberField E] [NumberField.IsCMField E] in
/-- The full rational Tate preimage of the constructed scalar is the
product of the inverse-power lattices at all chosen and opposite blocks. -/
theorem scalar_framedTatePreimage
    (χ : Fin s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])
    (e : TateComparison.Rational.SplitTateFrame s P.abelian.scheme T q)
    (he : TateComparison.Rational.IsSplitActionFrame P T q χ e)
    (L : Fin s × Bool → Submodule ℤ_[q] (Fin 3 → ℚ_[q]))
    (hL : TateComparison.Rational.framedIntegralTateImage e = Submodule.pi Set.univ L)
    (b : NumberField.RingOfIntegers E) (a : Fin s × Bool → ℕ)
    (hlocal : ∀ i, ∃ u : ℤ_[q]ˣ, χ i b = (q : ℤ_[q]) ^ a i * u)
    (f : TateComparison.PELIsogenies.PELIsogeny P P m) (hf : f.isogeny.hom = Scalar.Construction.scalarMap P b) :
    TateLattices.Construction.framedTatePreimage T e f =
      Submodule.pi Set.univ (fun i => (TateComparison.HeckeKernel.qUnit q ^ (-(a i : ℤ))) • L i) := by
  have hmap : ∀ z : TateComparison.Rational.SplitTateSpace s q, ∀ i,
      FramedTate.Construction.framedRationalTateMap T q e e f z i = (χ i b : ℚ_[q]) • z i := by
    intro z i
    have hf' := FramedTate.Construction.rationalTateMap_congr T q _ _ hf
    ext j
    change e (TateComparison.Rational.rationalTateMap (T := T) (q := q) f.isogeny.hom (e.symm z)) i j =
      (χ i b : ℚ_[q]) * z i j
    rw [hf']
    have hh := he b (e.symm z) i j
    rw [e.apply_symm_apply] at hh
    exact hh
  rw [TateLattices.Construction.framedTatePreimage_eq_comap T e e f, hL]
  apply Submodule.ext
  intro z
  change (∀ i ∈ Set.univ, FramedTate.Construction.framedRationalTateMap T q e e f z i ∈ L i) ↔
    ∀ i ∈ Set.univ, z i ∈ (TateComparison.HeckeKernel.qUnit q ^ (-(a i : ℤ))) • L i
  apply forall_congr'
  intro i
  apply forall_congr'
  intro _
  obtain ⟨u, hu⟩ := hlocal i
  have hv : (χ i b : ℚ_[q]) = (q : ℚ_[q]) ^ a i * (u : ℤ_[q]) := by
    have h := congrArg (algebraMap ℤ_[q] ℚ_[q]) hu
    rw [map_mul, map_pow, map_natCast] at h
    exact h
  rw [hmap, hv]
  exact padic_scalar_lattice_preimage q (L i) (a i) u (z i)

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ScalarTateLattice.Construction
