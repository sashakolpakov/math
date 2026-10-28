import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusFormEvaluation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.TensorExterior

/-! # Frobenius Form Square -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusFormSquare.BigPolynomialFrobeniusFormSquare

noncomputable section

/-! # The original polynomial Frobenius evaluation square on all relative frame forms -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

private theorem component_surjective (S : Type u) [CommRing S]
    {K L : CochainComplex (ModuleCat.{u} S) ℕ} (c : K ≅ L) (j : ℕ) :
    Function.Surjective (c.hom.f j).hom := by
  intro y
  refine ⟨(c.inv.f j).hom y, ?_⟩
  have h : c.inv.f j ≫ c.hom.f j = 𝟙 (L.X j) := congrArg (fun f => f.f j) c.inv_hom_id
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) y

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]
  [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ring p k σ
local notation "I" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ideal p k σ
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.dividedPowers p k σ
local notation "G" => fun n => DividedPowerAlgebra (R n) (σ →₀ R n)
local notation "IG" => fun n => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal (R n) σ (I n)
local notation "γ" => fun n => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers (R n) σ (I n) (δ n)

def coordinates (n j : ℕ) : Koszul.Tensor.KoszulTensor.Term W σ (G n) j →+
    PD.DeRham.PDDeRham.Form (R n) (G n) (IG n) (γ n) j :=
  ((FreeRelative.ScalarComparison.FreeRelativeScalarComparison.complexIso W (R n) σ (I n) (δ n)).hom.f j).hom.toAddMonoidHom

omit [PerfectRing k p] in
theorem coordinates_surjective (n j : ℕ) : Function.Surjective (coordinates p k σ n j) :=
  component_surjective W (FreeRelative.ScalarComparison.FreeRelativeScalarComparison.complexIso W (R n) σ (I n) (δ n)) j

def frobenius (n j : ℕ) : PD.DeRham.PDDeRham.Form W (R n) (I n) (δ n) j →+
    PD.DeRham.PDDeRham.Form W (R n) (I n) (δ n) j :=
  (WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.formsMap p k σ n j).toAddMonoidHom

def geometric (n j : ℕ) : PD.DeRham.PDDeRham.Form (R n) (G n) (IG n) (γ n) j →+
    PD.DeRham.PDDeRham.Form W (R n) (I n) (δ n) j :=
  (FrobeniusFormEvaluation.BigPolynomialFrobeniusFormEvaluation.evaluation p k σ n j).comp
    ((FrobeniusFormEvaluation.BigPolynomialFrobeniusFormEvaluation.power p k σ n j).comp
      (FrobeniusFormEvaluation.BigPolynomialFrobeniusFormEvaluation.ambient p k σ n j))

def explicit (n j : ℕ) : PD.DeRham.PDDeRham.Form (R n) (G n) (IG n) (γ n) j →+
    PD.DeRham.PDDeRham.Form W (R n) (I n) (δ n) j :=
  (frobenius p k σ n j).comp (FrobeniusFormEvaluation.BigPolynomialFrobeniusFormEvaluation.evaluation p k σ n j)

theorem square (n j : ℕ) : geometric p k σ n j = explicit p k σ n j := by
  let f := (geometric p k σ n j).comp (coordinates p k σ n j)
  let g := (explicit p k σ n j).comp (coordinates p k σ n j)
  have h : f = g := TensorExterior.TensorExteriorAdditiveExt.ext W σ (G n)
    (PD.DeRham.PDDeRham.Form W (R n) (I n) (δ n) j) j f g (by
      intro b v
      have hc := FreeRelative.ScalarComparison.FreeRelativeScalarComparison.word W (R n) σ (I n) (δ n) j b v
      exact (congrArg (geometric p k σ n j) hc).trans
        ((FrobeniusFormEvaluation.BigPolynomialFrobeniusFormEvaluation.square_symbol p k σ n j b v).trans
          (congrArg (explicit p k σ n j) hc).symm))
  apply AddMonoidHom.ext
  intro ω
  obtain ⟨z, rfl⟩ := coordinates_surjective p k σ n j ω
  exact DFunLike.congr_fun h z

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusFormSquare.BigPolynomialFrobeniusFormSquare
