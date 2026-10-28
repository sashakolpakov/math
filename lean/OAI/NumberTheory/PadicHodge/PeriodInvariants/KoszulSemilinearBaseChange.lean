import OAI.NumberTheory.PadicHodge.PeriodInvariants.ExteriorSemilinearBaseChange
import OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap

/-! # Koszul Semilinear Base Change -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.KoszulSemilinearBaseChange

noncomputable section

/-! # Actual semilinear base change of tensor Koszul complexes -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor
open scoped TensorProduct

universe u
variable {R S M N σ : Type u} [CommRing R] [CommRing S]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
  [Fintype σ] [LinearOrder σ] {φ : R →+* S}
  (D : σ → Module.End R M) (E : σ → Module.End S N) (f : M →ₛₗ[φ] N)
  (hf : ∀ i x, f (D i x) = E i (f x))

def termMap (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.Term R σ M n →ₛₗ[φ] AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.Term S σ N n :=
  TensorProduct.map f (ExteriorSemilinearBaseChange.exteriorMap φ n)

include hf in
theorem differential_commutes (n : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.Term R σ M n) :
    termMap f (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.differential R σ M D n x) =
      AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.differential S σ N E n (termMap f n x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m ω =>
    change termMap f (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.differential R σ M D n (m ⊗ₜ[R] ω)) =
      AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.differential S σ N E n (f m ⊗ₜ[S] ExteriorSemilinearBaseChange.exteriorMap φ n ω)
    rw [AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.differential_tmul, AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.differential_tmul, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change f (D i m) ⊗ₜ[S] ExteriorSemilinearBaseChange.exteriorMap φ (n + 1)
      (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.exteriorWedge R σ i n ω) = E i (f m) ⊗ₜ[S]
        AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.exteriorWedge S σ i n (ExteriorSemilinearBaseChange.exteriorMap φ n ω)
    rw [hf, ExteriorSemilinearBaseChange.wedge_commutes]

variable (hD : ∀ i j, Function.Commute (D i) (D j)) (hE : ∀ i j, Function.Commute (E i) (E j))

def complexMap : SemilinearComplexMap.Map φ (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.complex R σ M D hD) (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.complex S σ N E hE) :=
  SemilinearComplexMap.ofSuccessors (termMap f) (fun n x => by
    have hd : (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.complex R σ M D hD).d n (n + 1) = ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.differential R σ M D n) :=
      CochainComplex.of_d (fun k => ModuleCat.of R (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.Term R σ M k))
        (fun k => ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.differential R σ M D k)) n
    have he : (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.complex S σ N E hE).d n (n + 1) = ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.differential S σ N E n) :=
      CochainComplex.of_d (fun k => ModuleCat.of S (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.Term S σ N k))
        (fun k => ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.differential S σ N E k)) n
    exact (congrArg (fun k : ModuleCat.of R (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.Term R σ M n) ⟶ ModuleCat.of R (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.Term R σ M (n + 1)) =>
      termMap f (n + 1) (k.hom x)) hd).trans
        ((differential_commutes D E f hf n x).trans
          (congrArg (fun k : ModuleCat.of S (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.Term S σ N n) ⟶ ModuleCat.of S (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.Term S σ N (n + 1)) =>
            k.hom (termMap f n x)) he).symm))

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.KoszulSemilinearBaseChange
