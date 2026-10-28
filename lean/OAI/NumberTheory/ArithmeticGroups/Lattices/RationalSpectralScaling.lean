import OAI.NumberTheory.ArithmeticGroups.Lattices.EigenbasisMatrixSpectral
import OAI.NumberTheory.ArithmeticGroups.Lattices.NormalizedTraceSpectrum
import OAI.NumberTheory.ArithmeticGroups.Lattices.SpectralGaloisDescent
import OAI.NumberTheory.ArithmeticGroups.Lattices.SemisimpleScalingElement

/-! # Rational Spectral Scaling -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.RationalSpectralScaling.Construction

noncomputable section

/-! Normalized trace replaces the semisimple scaling element by a
rational-spectrum matrix that is still defined over the number field. -/

open scoped Classical

attribute [local instance] LieRing.ofAssociativeRing

theorem semisimple_scaling_has_rational_spectrum
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected)
    (S A : Matrix (Fin n) (Fin n) k) (hS : S ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G)
    (hsemi : Module.End.IsSemisimple (Matrix.toLin' S)) (hscale : S * A - A * S = A) :
    ∃ T ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G,
      T * A - A * T = A ∧
      ∃ (b : Module.Basis (Fin n) (AlgebraicClosure k) (Fin n → AlgebraicClosure k))
        (w : Fin n → ℚ),
        ∀ i, Matrix.toLin' (T.map (algebraMap k (AlgebraicClosure k))) (b i) =
          algebraMap ℚ (AlgebraicClosure k) (w i) • b i := by
  let K := AlgebraicClosure k
  let : Algebra.IsIntegral ℚ K := Algebra.IsIntegral.trans k
  let ι := algebraMap k K
  obtain ⟨b, w, hb⟩ := SemisimpleMatrixDiagonalization.Construction.semisimple_matrix_has_eigenbasis (S.map ι)
    (SemisimpleMatrixDiagonalization.Construction.semisimple_matrix_coefficient_map ι S hsemi)
  let ψ : K →+ K := NormalizedTraceSpectrum.Construction.normalizedTraceSpectralMap (k := ℚ)
  let T := EigenbasisMatrixSpectral.Construction.eigenbasisSpectralMatrix b (fun i => ψ (w i))
  have hT (i : Fin n) : Matrix.toLin' T (b i) = ψ (w i) • b i :=
    EigenbasisMatrixSpectral.Construction.eigenbasisSpectralMatrix_apply b _ i
  obtain ⟨T₀, hT₀⟩ := SpectralGaloisDescent.Construction.matrix_spectral_function_descends b S T w ψ hb hT
    (fun σ x => NormalizedTraceSpectrum.Construction.rational_normalizedTraceSpectralMap_equivariant σ x)
  have hT₀' : T₀.map ι = T := hT₀
  have hTmem : T ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G ι) :=
    EigenbasisMatrixSpectral.Construction.infinitesimal_eigenbasis_spectral_matrix (BaseChange.Construction.matrixGroupBaseChange G ι) b (S.map ι) w ψ hb
      (CharZeroTangent.Construction.infinitesimalStabilizer_coefficient_map G hconn hS)
  have hT₀mem : T₀ ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G :=
    Infinitesimal.JordanDescent.Construction.infinitesimalStabilizer_descends_coefficient_map ι G hconn T₀ (hT₀.symm ▸ hTmem)
  refine ⟨T₀, hT₀mem, ?_, b, fun i => Algebra.normalizedTrace ℚ K (w i), ?_⟩
  · let e : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K) := Matrix.toLinAlgEquiv'
    have hscaleK : S.map ι * A.map ι - A.map ι * S.map ι = A.map ι := by
      simpa only [map_sub, map_mul, RingHom.mapMatrix_apply] using
        congrArg (ι.mapMatrix : Matrix (Fin n) (Fin n) k →+* Matrix (Fin n) (Fin n) K) hscale
    have hscaleEnd : ⁅e (S.map ι), e (A.map ι)⁆ = (1 : K) • e (A.map ι) := by
      change e (S.map ι) * e (A.map ι) - e (A.map ι) * e (S.map ι) = _
      rw [← map_mul, ← map_mul, ← map_sub, hscaleK, one_smul]
    have h := AdditiveSpectralScaling.Construction.additive_spectral_bracket_scaling b (e (S.map ι)) (e T) (e (A.map ι))
      w ψ hb hT 1 hscaleEnd
    have hbr : T * A.map ι - A.map ι * T = A.map ι := by
      apply e.injective
      simpa only [ψ, NormalizedTraceSpectrum.Construction.normalizedTraceSpectralMap_one, one_smul, Ring.lie_def, map_sub, map_mul] using h
    have hm : (T₀ * A - A * T₀).map ι = A.map ι := by
      change ι.mapMatrix (T₀ * A - A * T₀) = ι.mapMatrix A
      simpa only [map_sub, map_mul, RingHom.mapMatrix_apply, hT₀'] using hbr
    ext i j : 1
    exact ι.injective (congrFun (congrFun hm i) j)
  · intro i
    rw [hT₀]
    exact hT i

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.RationalSpectralScaling.Construction
