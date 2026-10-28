import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FiniteFreeComplex
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # Finite Projective Complex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FiniteProjectiveComplex.CochainFiniteModel

noncomputable section

/-! The finite model over an arbitrary Noetherian base has projective terms.
Only the final passage from projective to free requires a local ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

theorem exists_finite_projective_complex (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hbound : ∃ N, ∀ q, N ≤ q → IsZero (C.X q))
    (hflat : ∀ q, Module.Flat R (C.X q))
    (hfinite : ∀ q, Module.Finite R (C.homology q)) :
    ∃ (D : CochainComplex (ModuleCat.{u} R) ℕ) (φ : D ⟶ C),
      QuasiIso φ ∧
      (∃ N, ∀ q, N ≤ q → IsZero (D.X q)) ∧
      (∀ q, Module.Finite R (D.X q)) ∧
      (∀ q, Module.Projective R (D.X q)) ∧
      (∀ (A : Type u) [AddCommGroup A] [Module R A],
        QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map A φ)) := by
  obtain ⟨N, hN⟩ := hbound
  obtain ⟨M⟩ := FlatModel.CochainFiniteModel.exists_model C N hN hflat (fun q => hfinite (q + 1))
  have := hfinite 0
  have hfin : ∀ q, Module.Finite R (M.complex.X q) := by
    intro q
    cases q with
    | zero => exact M.first_finite
    | succ q => exact M.finite q
  refine ⟨M.complex, M.comparison, M.quasiIso, M.bounded, hfin, ?_, M.tensor_quasiIso⟩
  intro q
  have := hfin q
  have := M.flat q
  have : Module.FinitePresentation R (M.complex.X q) :=
    Module.finitePresentation_of_finite R (M.complex.X q)
  exact Module.Flat.projective_of_finitePresentation

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FiniteProjectiveComplex.CochainFiniteModel
