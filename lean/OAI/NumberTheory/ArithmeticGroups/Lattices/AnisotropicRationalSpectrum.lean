import OAI.NumberTheory.ArithmeticGroups.Lattices.DiagonalConjugatorNormalization
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Rat

/-! # Anisotropic Rational Spectrum -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AnisotropicRationalSpectrum.Construction

noncomputable section

/-! Clearing rational eigenvalue denominators turns a split
infinitesimal matrix into integer cocharacter weights. -/

open scoped Classical

attribute [local instance] LieRing.ofAssociativeRing

theorem finite_rational_weights_integer_multiple
    {ι : Type*} [Finite ι] (w : ι → ℚ) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ z : ι → ℤ, ∀ i, (z i : ℚ) = (d : ℚ) * w i := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) w
  choose z hz using hd
  refine ⟨d.val, mem_nonZeroDivisors_iff_ne_zero.mp d.property, z, fun i => ?_⟩
  have hi : (z i : ℚ) = d.val • w i := hz i
  simpa only [zsmul_eq_mul] using hi

theorem anisotropic_rational_eigenbasis_matrix_zero
    {k : Type} [Field k] [CharZero k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G) (A : Matrix (Fin G.dimension) (Fin G.dimension) k)
    (hA : A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G.matrixGroup)
    (b : Module.Basis (Fin G.dimension) k (Fin G.dimension → k)) (w : Fin G.dimension → ℚ)
    (hb : ∀ i, Matrix.toLin' A (b i) = (w i : k) • b i) : A = 0 := by
  obtain ⟨d, hd, z, hz⟩ := finite_rational_weights_integer_multiple w
  have hdk : (d : k) ≠ 0 := Int.cast_ne_zero.mpr hd
  have hcast (i) : (z i : k) = (d : k) * (w i : k) := by
    exact_mod_cast hz i
  have hscaled (i) : Matrix.toLin' ((d : k) • A) (b i) = (z i : k) • b i := by
    rw [map_smul, LinearMap.smul_apply, hb i, smul_smul, ← hcast i]
  let g := EigenbasisMatrixSpectral.Construction.eigenbasisMatrixUnit b
  have heq : (d : k) • A = g.val * Matrix.diagonal (fun i => (z i : k)) * (g⁻¹).val :=
    EigenbasisMatrixSpectral.Construction.matrix_eq_eigenbasis_conjugate _ b _ hscaled
  have hmem : g.val * Matrix.diagonal (fun i => (z i : k)) * (g⁻¹).val ∈
      Infinitesimal.Action.Construction.infinitesimalStabilizer G.matrixGroup := by
    rw [← heq]
    exact (Infinitesimal.Action.Construction.infinitesimalStabilizer G.matrixGroup).smul_mem (d : k) hA
  have hz0 := DiagonalConjugatorNormalization.Construction.anisotropic_unit_conjugated_integer_weights_zero G haniso g z hmem
  have hzero : (d : k) • A = 0 := by
    rw [heq, hz0]
    simp
  exact (smul_eq_zero.mp hzero).resolve_left hdk

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AnisotropicRationalSpectrum.Construction
