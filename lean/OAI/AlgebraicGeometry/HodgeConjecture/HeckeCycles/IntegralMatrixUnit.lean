import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.MatrixPivot
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticLocal

/-! # Integral Matrix Unit -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IntegralMatrixUnit.CM

noncomputable section

/-! An adelic matrix unit and its inverse are integral at almost all
places, where they define an actual matrix unit over the local integers. -/

open scoped Classical _root_.Matrix RestrictedProduct
open Filter
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticLocal.CM

variable {I R : Type*} [Fintype I] [CommRing R]

def liftMatrix (S : Subring R) (M : Matrix I I R) (hM : ∀ i j, M i j ∈ S) : Matrix I I S :=
  fun i j => ⟨M i j, hM i j⟩

omit [Fintype I] in
theorem liftMatrix_map (S : Subring R) (M : Matrix I I R) (hM : ∀ i j, M i j ∈ S) :
    (liftMatrix S M hM).map S.subtype = M := rfl

def subringUnit (S : Subring R) (A : (Matrix I I R)ˣ)
    (hA : ∀ i j, A.val i j ∈ S) (hInv : ∀ i j, (A⁻¹).val i j ∈ S) : (Matrix I I S)ˣ where
  val := liftMatrix S A.val hA
  inv := liftMatrix S (A⁻¹).val hInv
  val_inv := by
    apply Matrix.map_injective S.subtype_injective
    dsimp only
    rw [Matrix.map_mul, liftMatrix_map, liftMatrix_map]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    exact S.subtype.mapMatrix.map_one.symm
  inv_val := by
    apply Matrix.map_injective S.subtype_injective
    dsimp only
    rw [Matrix.map_mul, liftMatrix_map, liftMatrix_map]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact S.subtype.mapMatrix.map_one.symm

def localUnit (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : (Matrix I I (v.adicCompletion ℚ))ˣ :=
  Units.map (Finite.SymplecticLocal.CM.localEval v).mapMatrix.toMonoidHom A

def IsIntegral (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : Prop :=
  (∀ i j, A.val i j v ∈ v.adicCompletionIntegers ℚ) ∧
    ∀ i j, (A⁻¹).val i j v ∈ v.adicCompletionIntegers ℚ

theorem eventually_integral (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) : ∀ᶠ v in cofinite, IsIntegral A v := by
  apply Filter.Eventually.and
  · exact Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => (A.val i j).property
  · exact Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => ((A⁻¹).val i j).property

def integralUnit (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hA : IsIntegral A v) :
    (Matrix I I (v.adicCompletionIntegers ℚ))ˣ :=
  subringUnit (v.adicCompletionIntegers ℚ).toSubring (localUnit A v) hA.1 hA.2

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IntegralMatrixUnit.CM
