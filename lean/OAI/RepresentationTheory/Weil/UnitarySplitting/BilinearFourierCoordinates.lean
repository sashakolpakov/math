import OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticCutoffNe
import OAI.RepresentationTheory.Weil.UnitarySplitting.NormPolarForm

/-! # Bilinear Fourier Coordinates -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.BilinearFourierCoordinates.Construction

noncomputable section

section

/-! Continuous bilinear coordinates and the shift solving completion of
the square for every Fourier frequency. -/

def finiteBilinearContinuous
    {F V : Type} [NontriviallyNormedField F] [CompleteSpace F]
    [NormedAddCommGroup V] [NormedSpace F V] [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V) : V →L[F] V →L[F] F :=
  (LinearMap.toContinuousLinearMap.toLinearMap.comp B).toContinuousLinearMap

theorem finiteBilinearContinuous_apply
    {F V : Type} [NontriviallyNormedField F] [CompleteSpace F]
    [NormedAddCommGroup V] [NormedSpace F V] [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V) (x y : V) : finiteBilinearContinuous B x y = B x y := rfl

theorem exists_gaussian_fourier_shift
    {F : Type} [NontriviallyNormedField F] [CompleteSpace F] {d : ℕ}
    (B : LinearMap.BilinForm F (Local.FunctionsMetaplectic.Construction.Position F d)) (hB : B.Nondegenerate) :
    ∃ A : Local.FunctionsMetaplectic.Construction.Position F d →L[F] Local.FunctionsMetaplectic.Construction.Position F d, ∀ y x, finiteBilinearContinuous B (A y) x = -Local.FunctionsMetaplectic.Construction.dot y x := by
  let D : LinearMap.BilinForm F (Local.FunctionsMetaplectic.Construction.Position F d) := -dotProductBilin F F
  let A := D.symmCompOfNondegenerate B hB
  refine ⟨A.toContinuousLinearMap, fun y x => ?_⟩
  change B (A y) x = -Local.FunctionsMetaplectic.Construction.dot y x
  have hh := D.symmCompOfNondegenerate_left_apply hB x y
  exact hh

end

/-! A nondegenerate bilinear Fourier transform is a coordinate Fourier
transform composed with an invertible linear change of frequency. -/

open _root_.MeasureTheory

theorem exists_gaussian_fourier_shift_equiv
    {F : Type} [NontriviallyNormedField F] [CompleteSpace F] {d : ℕ}
    (B : LinearMap.BilinForm F (Local.FunctionsMetaplectic.Construction.Position F d)) (hB : B.Nondegenerate) :
    ∃ A : Local.FunctionsMetaplectic.Construction.Position F d ≃L[F] Local.FunctionsMetaplectic.Construction.Position F d, ∀ y x, B (A y) x = -Local.FunctionsMetaplectic.Construction.dot y x := by
  obtain ⟨A, hA⟩ := exists_gaussian_fourier_shift B hB
  have hinj : Function.Injective A := by
    intro x y hxy
    funext i
    have hh := congrArg (fun z => finiteBilinearContinuous B z (Pi.single i 1)) hxy
    rw [hA, hA] at hh
    simpa only [Local.FunctionsMetaplectic.Construction.dot, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, neg_inj] using hh
  have hsurj : Function.Surjective A.toLinearMap :=
    (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp hinj
  let e := (LinearEquiv.ofBijective A.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  refine ⟨e, fun y x => ?_⟩
  exact hA y x

theorem bilinear_fourier_coordinate_formula
    {F V : Type} [NormedField F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] [NormedAddCommGroup V] [Module F V]
    [MeasurableSpace V] [BorelSpace V] {d : ℕ}
    (e : V ≃L[F] Local.FunctionsMetaplectic.Construction.Position F d) (B : LinearMap.BilinForm F V)
    (A : Local.FunctionsMetaplectic.Construction.Position F d ≃L[F] Local.FunctionsMetaplectic.Construction.Position F d)
    (hA : ∀ p x, B (e.symm (A p)) (e.symm x) = -Local.FunctionsMetaplectic.Construction.dot p x)
    (L : V ≃L[F] V) (ψ : AddChar F ℂ) (μ : Measure V) (f : V → ℂ) (v : V) :
    (∫ x, ψ (B (L v) x) * f x ∂μ) =
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (μ.map e) (fun x => f (e.symm x)) (A.symm (e (L v))) := by
  unfold Local.FunctionsMetaplectic.Construction.fourierIntegral
  change _ = ∫ x, f (e.symm x) * ψ (-Local.FunctionsMetaplectic.Construction.dot (A.symm (e (L v))) x) ∂μ.map e.toHomeomorph
  rw [e.toHomeomorph.isClosedEmbedding.integral_map]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change ψ (B (L v) x) * f x = f (e.symm (e x)) * ψ (-Local.FunctionsMetaplectic.Construction.dot (A.symm (e (L v))) (e x))
    have hb := hA (A.symm (e (L v))) (e x)
    rw [A.apply_symm_apply, e.symm_apply_apply, e.symm_apply_apply] at hb
    rw [e.symm_apply_apply, ← hb, mul_comm]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.BilinearFourierCoordinates.Construction
