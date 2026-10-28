import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteTensorIntertwiner
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # Equivariant Koszul -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.EquivariantKoszul

noncomputable section

/-! # The Koszul complex as an actual complex of continuous representations -/

open _root_.CategoryTheory TopRep OAI.NumberTheory.PadicHodge.PeriodInvariants.ContinuousOrbit.PiRepresentation OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteTensorCoordinates

universe u
variable {R G σ : Type u} [CommRing R] [TopologicalSpace R] [Group G]
  [Fintype σ] [LinearOrder σ] (X : TopRep.{u} R G)

abbrev Index (n : ℕ) := Set.powersetCard σ n

def exteriorBasis (n : ℕ) : Module.Basis (Index (σ := σ) n) R (⋀[R]^n (σ →₀ R)) :=
  (Finsupp.basisSingleOne : Module.Basis σ R (σ →₀ R)).exteriorPower n

def term (n : ℕ) : TopRep.{u} R G := TopRep.of (ContinuousOrbit.PiRepresentation.piRepresentation (I := Index (σ := σ) n) X.ρ)

def termCoordinates (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.Term R σ X n ≃ₗ[R] term (σ := σ) X n :=
  FiniteTensorCoordinates.coordinates (exteriorBasis (R := R) (σ := σ) n)

def underlyingAddHom (Y Z : TopRep.{u} R G) : (Y ⟶ Z) →+ (Y →L[R] Z) where
  toFun f := f.hom.toContinuousLinearMap
  map_zero' := rfl
  map_add' _ _ := rfl

variable (D : σ → (X ⟶ X))

def linearD (i : σ) : Module.End R X := (D i).hom.toContinuousLinearMap.toLinearMap

def differential (n : ℕ) : term (σ := σ) X n ⟶ term (σ := σ) X (n + 1) :=
  ∑ i, TopRep.ofHom (FiniteTensorIntertwiner.matrixIntertwiner
    (exteriorBasis (R := R) (σ := σ) n) (exteriorBasis (R := R) (σ := σ) (n + 1))
    (D i).hom (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.exteriorWedge R σ i n))

theorem differential_coordinates (n : ℕ) (z : AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.Term R σ X n) :
    (differential X D n).hom (termCoordinates X n z) =
      termCoordinates X (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.differential R σ X (linearD X D) n z) := by
  have hm : (differential X D n).hom.toContinuousLinearMap =
      ∑ i, FiniteTensorCoordinates.matrixMap (exteriorBasis (R := R) (σ := σ) n)
        (exteriorBasis (R := R) (σ := σ) (n + 1)) (D i).hom.toContinuousLinearMap
        (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.exteriorWedge R σ i n) :=
    map_sum (underlyingAddHom (term (σ := σ) X n) (term (σ := σ) X (n + 1))) _ _
  apply (DFunLike.congr_fun hm (termCoordinates X n z)).trans
  let ev : ((Index (σ := σ) n → X) →L[R] (Index (σ := σ) (n + 1) → X)) →+
      (Index (σ := σ) (n + 1) → X) := {
    toFun f := f (termCoordinates X n z)
    map_zero' := rfl
    map_add' _ _ := rfl }
  apply (map_sum ev (fun i => FiniteTensorCoordinates.matrixMap (exteriorBasis (R := R) (σ := σ) n)
    (exteriorBasis (R := R) (σ := σ) (n + 1)) (D i).hom.toContinuousLinearMap
      (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.exteriorWedge R σ i n)) Finset.univ).trans
  simp only [AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.differential, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact FiniteTensorCoordinates.matrixMap_coordinates (exteriorBasis (R := R) (σ := σ) n)
    (exteriorBasis (R := R) (σ := σ) (n + 1)) (D i).hom.toContinuousLinearMap
    (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.exteriorWedge R σ i n) z

variable (hD : ∀ i j, Function.Commute (linearD X D i) (linearD X D j))

include hD in
theorem differential_square (n : ℕ) : differential X D n ≫ differential X D (n + 1) = 0 := by
  apply TopRep.hom_ext
  apply ContIntertwiningMap.ext
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨z, rfl⟩ := (termCoordinates (σ := σ) X n).surjective v
  have h₁ := differential_coordinates X D n z
  have h₂ := differential_coordinates X D (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.differential R σ X (linearD X D) n z)
  have hz := LinearMap.congr_fun (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.differential_square_linear R σ X (linearD X D) hD n) z
  exact (congrArg (differential X D (n + 1)).hom h₁).trans
    (h₂.trans ((congrArg (termCoordinates (σ := σ) X (n + 2)) hz).trans (map_zero _)))

def complex : CochainComplex (TopRep.{u} R G) ℕ :=
  CochainComplex.of (term (σ := σ) X) (differential X D) (differential_square X D hD)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.EquivariantKoszul
