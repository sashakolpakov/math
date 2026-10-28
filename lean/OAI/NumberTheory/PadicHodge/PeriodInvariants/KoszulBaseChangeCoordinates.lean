import OAI.NumberTheory.PadicHodge.PeriodInvariants.KoszulSemilinearBaseChange
import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteTensorCoordinates

/-! # Koszul Base Change Coordinates -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.KoszulBaseChangeCoordinates

noncomputable section

/-! # Coordinates, surjectivity, and scalar kernels of actual Koszul base change -/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.EquivariantKoszul OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteTensorCoordinates OAI.NumberTheory.PadicHodge.PeriodInvariants.KoszulSemilinearBaseChange
open OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor
open scoped TensorProduct

universe u
variable {R S M N σ : Type u} [CommRing R] [CommRing S]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
  [Fintype σ] [LinearOrder σ] {φ : R →+* S} (f : M →ₛₗ[φ] N)

theorem coordinates_commutes (n : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.Term R σ M n) :
    FiniteTensorCoordinates.coordinates (EquivariantKoszul.exteriorBasis (R := S) (σ := σ) n) (KoszulSemilinearBaseChange.termMap f n x) =
      fun i => f (FiniteTensorCoordinates.coordinates (EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n) x i) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    funext i
    simp only [map_add, Pi.add_apply]
    exact congrArg₂ (· + ·) (congrFun hx i) (congrFun hy i)
  | tmul m ω =>
    funext i
    change FiniteTensorCoordinates.coordinates (EquivariantKoszul.exteriorBasis (R := S) (σ := σ) n)
      (f m ⊗ₜ[S] ExteriorSemilinearBaseChange.exteriorMap φ n ω) i =
        f (FiniteTensorCoordinates.coordinates (EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n) (m ⊗ₜ[R] ω) i)
    rw [FiniteTensorCoordinates.coordinates_tmul, FiniteTensorCoordinates.coordinates_tmul, ExteriorSemilinearBaseChange.exteriorMap_repr,
      f.map_smulₛₗ]

theorem surjective (hf : Function.Surjective f) (n : ℕ) : Function.Surjective (KoszulSemilinearBaseChange.termMap (σ := σ) f n) := by
  intro y
  let cR := FiniteTensorCoordinates.coordinates (M := M) (EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n)
  let cS := FiniteTensorCoordinates.coordinates (M := N) (EquivariantKoszul.exteriorBasis (R := S) (σ := σ) n)
  let v : Set.powersetCard σ n → M := fun i => (hf (cS y i)).choose
  refine ⟨cR.symm v, ?_⟩
  apply cS.injective
  apply (coordinates_commutes f n (cR.symm v)).trans
  funext i
  change f (cR (cR.symm v) i) = cS y i
  rw [LinearEquiv.apply_symm_apply]
  exact (hf (cS y i)).choose_spec

variable (a : R) (hker : ∀ x, f x = 0 ↔ ∃ y, a • y = x)

include hker in
theorem kernel (n : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.Term R σ M n) : KoszulSemilinearBaseChange.termMap f n x = 0 ↔ ∃ y, a • y = x := by
  let cR := FiniteTensorCoordinates.coordinates (M := M) (EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n)
  let cS := FiniteTensorCoordinates.coordinates (M := N) (EquivariantKoszul.exteriorBasis (R := S) (σ := σ) n)
  constructor
  · intro hx
    have hc : ∀ i, f (cR x i) = 0 := by
      intro i
      have h := congrFun (coordinates_commutes f n x) i
      exact h.symm.trans ((congrArg (fun z => cS z i) hx).trans (congrFun (map_zero cS) i))
    let v : Set.powersetCard σ n → M := fun i => ((hker (cR x i)).mp (hc i)).choose
    refine ⟨cR.symm v, ?_⟩
    apply cR.injective
    rw [map_smul, LinearEquiv.apply_symm_apply]
    funext i
    exact ((hker (cR x i)).mp (hc i)).choose_spec
  · rintro ⟨y, rfl⟩
    apply cS.injective
    rw [map_zero]
    apply (coordinates_commutes f n (a • y)).trans
    funext i
    apply (hker _).mpr
    exact ⟨cR y i, (congrFun (map_smul cR a y) i).symm⟩

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.KoszulBaseChangeCoordinates
