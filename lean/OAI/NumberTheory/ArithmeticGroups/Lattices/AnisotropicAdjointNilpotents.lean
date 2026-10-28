import OAI.NumberTheory.ArithmeticGroups.Lattices.RationalSpectralScaling
import OAI.NumberTheory.ArithmeticGroups.Lattices.RationalEigenbasisDescent
import OAI.NumberTheory.ArithmeticGroups.Lattices.AnisotropicRationalSpectrum

/-! # Anisotropic Adjoint Nilpotents -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AnisotropicAdjointNilpotents.Construction

noncomputable section

section

/-! The cocharacter definition of anisotropy excludes nonzero nilpotent
matrices in the rational Lie algebra of a semisimple algebraic group. -/

open scoped Classical

theorem anisotropic_infinitesimal_nilpotent_eq_zero
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G) (A : Matrix (Fin G.dimension) (Fin G.dimension) k)
    (hA : A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G.matrixGroup) (hnil : IsNilpotent A) : A = 0 := by
  obtain ⟨S, hS, hsemi, hscale⟩ := SemisimpleScalingElement.Construction.infinitesimal_nilpotent_has_semisimple_scaling_matrix
    G.matrixGroup G.connected G.semisimple hA hnil
  obtain ⟨T, hT, hTA, b, w, hb⟩ := RationalSpectralScaling.Construction.semisimple_scaling_has_rational_spectrum
    G.matrixGroup G.connected S A hS hsemi hscale
  obtain ⟨b₀, w₀, hb₀⟩ := RationalEigenbasisDescent.Construction.rational_eigenbasis_descends T b w hb
  have hzero := AnisotropicRationalSpectrum.Construction.anisotropic_rational_eigenbasis_matrix_zero G haniso T hT b₀ w₀ hb₀
  simpa only [hzero, zero_mul, mul_zero, sub_self] using hTA.symm

end

/-! Anisotropy excludes nonzero elements with nilpotent intrinsic
adjoint action, independently of the chosen matrix representation. -/

open scoped Classical

attribute [local instance] LieRing.ofAssociativeRing

theorem infinitesimal_scaling_has_semisimple_scaling_matrix
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (H A : Matrix (Fin n) (Fin n) k) (hH : H ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G)
    (hscale : H * A - A * H = A) :
    ∃ S ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G,
      Module.End.IsSemisimple (Matrix.toLin' S) ∧ S * A - A * S = A := by
  obtain ⟨N, _, S, hS, hNnil, hSsemi, hNS, hHNS⟩ :=
    SemisimpleScalingElement.Construction.infinitesimal_exists_jordan_decomposition G hG H hH
  refine ⟨S, hS, hSsemi, ?_⟩
  let e : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k) := Matrix.toLinAlgEquiv'
  have hscale' : ⁅e N + e S, e A⁆ = (1 : k) • e A := by
    change (e N + e S) * e A - e A * (e N + e S) = (1 : k) • e A
    rw [← map_add, ← map_mul, ← map_mul, ← map_sub, ← hHNS, hscale, one_smul]
  have hSscale := (JordanScaling.Construction.semisimple_summand_retains_bracket_scaling
    (e N) (e S) (e A) (hNS.map e) (hNnil.map e) hSsemi 1 hscale').1
  apply e.injective
  simpa only [map_sub, map_mul, Ring.lie_def, one_smul] using hSscale

theorem anisotropic_infinitesimal_scaling_eq_zero
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G)
    (H A : Matrix (Fin G.dimension) (Fin G.dimension) k)
    (hH : H ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G.matrixGroup) (hscale : H * A - A * H = A) : A = 0 := by
  obtain ⟨S, hS, hsemi, hSA⟩ := infinitesimal_scaling_has_semisimple_scaling_matrix
    G.matrixGroup G.connected H A hH hscale
  obtain ⟨T, hT, hTA, b, w, hb⟩ := RationalSpectralScaling.Construction.semisimple_scaling_has_rational_spectrum
    G.matrixGroup G.connected S A hS hsemi hSA
  obtain ⟨b₀, w₀, hb₀⟩ := RationalEigenbasisDescent.Construction.rational_eigenbasis_descends T b w hb
  have hzero := AnisotropicRationalSpectrum.Construction.anisotropic_rational_eigenbasis_matrix_zero G haniso T hT b₀ w₀ hb₀
  simpa only [hzero, zero_mul, mul_zero, sub_self] using hTA.symm

theorem anisotropic_infinitesimal_ad_nilpotent_eq_zero
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G) (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G.matrixGroup)
    (hnil : _root_.IsNilpotent (LieAlgebra.ad k (Infinitesimal.Action.Construction.infinitesimalStabilizer G.matrixGroup) A)) : A = 0 := by
  let : LieAlgebra.IsKilling k (Infinitesimal.Action.Construction.infinitesimalStabilizer G.matrixGroup) :=
    KillingScalarDescent.Construction.infinitesimal_isKilling G.matrixGroup G.connected G.semisimple
  obtain ⟨H, hH⟩ := JordanScaling.Construction.exists_lie_eq_self_of_nilpotent_ad A hnil
  apply Subtype.ext
  apply anisotropic_infinitesimal_scaling_eq_zero G haniso H.val A.val H.property
  exact congrArg (fun X : Infinitesimal.Action.Construction.infinitesimalStabilizer G.matrixGroup => X.val) hH

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AnisotropicAdjointNilpotents.Construction
