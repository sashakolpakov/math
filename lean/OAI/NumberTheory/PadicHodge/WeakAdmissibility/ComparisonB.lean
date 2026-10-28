import OAI.NumberTheory.PadicHodge.WeakAdmissibility.ValuationStructure
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.CrystallineEmbedding

/-! # Comparison B -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonB

noncomputable section

/-! The comparison uses the actual inclusion of the maximal unramified field. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.MaximalUnramified OAI.NumberTheory.PadicHodge.WeakAdmissibility.ValuationStructure OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField.Scalars
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonBd OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonScalars OAI.NumberTheory.PadicHodge.WeakAdmissibility.AlgebraicCoefficientFields
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientComparison OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteFieldResidue OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField.Constants
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.DcrisD OAI.NumberTheory.PadicHodge.WeakAdmissibility.DcrisCoefficients OAI.NumberTheory.PadicHodge.WeakAdmissibility.InvariantComparison
open scoped TensorProduct

theorem tensorMap_smul {R S B C W : Type*} [CommRing R] [CommRing S]
    [AddCommGroup B] [Module R B] [Module S B] [SMulCommClass R S B]
    [AddCommGroup C] [Module R C] [Module S C] [SMulCommClass R S C]
    [AddCommGroup W] [Module R W] (f : B →ₗ[R] C)
    (hf : ∀ (a : S) (b : B), f (a • b) = a • f b) (a : S) (x : B ⊗[R] W) :
    TensorProduct.map f (LinearMap.id : W →ₗ[R] W) (a • x) =
      a • TensorProduct.map f (LinearMap.id : W →ₗ[R] W) x := by
  induction x using TensorProduct.inductionOn with
  | tmul b v => simp only [TensorProduct.smul_tmul', TensorProduct.map_tmul, hf]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

variable (p : ℕ) [Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [Module.Finite ℚ_[p] K]

def k0ToK : MaximalUnramified.K0 p K →ₐ[ℚ_[p]] K := IntermediateField.inclusion (MaximalUnramified.K0_isGreatest p K).1.1

instance k0FieldAlgebra : Algebra (MaximalUnramified.K0 p K) K := (k0ToK p K).toRingHom.toAlgebra

instance k0FieldModule : Module (MaximalUnramified.K0 p K) K := Algebra.toModule

instance k0FieldTower : IsScalarTower ℚ_[p] (MaximalUnramified.K0 p K) K :=
  IsScalarTower.of_algebraMap_eq (fun a => ((k0ToK p K).commutes a).symm)

theorem k0ToBCris_comparison (a : MaximalUnramified.K0 p K) :
    ComparisonBd.bCrisToBdR p (ValuationStructure.k0ToBCris p K a) = DeRhamField.Scalars.fieldToDeRham p (MaximalUnramified.K0 p K) a := by
  change ComparisonBd.bCrisToBdR p (UnramifiedCoefficients.coefficientFieldToBCris p
    (FiniteFieldResidue.residueEmbedding p K) ((ValuationStructure.k0ModelEquiv p K).symm a)) =
      ComparisonBd.bdRPlusToBdR p (DeRhamField.Constants.algebraicToBdRPlus p (a : PadicAlgCl p))
  rw [CoefficientComparison.coefficientFieldToBCris_comparison, ← AlgebraicCoefficientFields.coefficientFieldToAlgebraic_completion]
  apply congrArg (fun z : PadicAlgCl p => ComparisonBd.bdRPlusToBdR p (DeRhamField.Constants.algebraicToBdRPlus p z))
  exact congrArg Subtype.val ((ValuationStructure.k0ModelEquiv p K).apply_symm_apply a)

theorem k0ToK_deRham (a : MaximalUnramified.K0 p K) :
    DeRhamField.Scalars.fieldToDeRham p K (k0ToK p K a) = DeRhamField.Scalars.fieldToDeRham p (MaximalUnramified.K0 p K) a := rfl

instance k0DeRhamFieldTower : IsScalarTower (MaximalUnramified.K0 p K) K (Logarithm.PeriodRings.BdR p) :=
  IsScalarTower.of_algebraMap_eq (fun a => (k0ToK_deRham p K a).symm)

instance k0PeriodDistrib : DistribMulAction (MaximalUnramified.K0 p K) (Logarithm.PeriodRings.BCris p) :=
  (ValuationStructure.k0PeriodModule p K).toDistribMulAction

instance k0PeriodAction : MulAction (MaximalUnramified.K0 p K) (Logarithm.PeriodRings.BCris p) := (k0PeriodDistrib p K).toMulAction

instance k0PeriodTower : IsScalarTower ℚ_[p] (MaximalUnramified.K0 p K) (Logarithm.PeriodRings.BCris p) :=
  IsScalarTower.of_algebraMap_eq (fun a => ((ValuationStructure.k0ToBCris p K).commutes a).symm)

instance k0PeriodComm : SMulCommClass ℚ_[p] (MaximalUnramified.K0 p K) (Logarithm.PeriodRings.BCris p) where
  smul_comm a b x := by
    change Galois.PeriodStructure.padicToBCris p a * (ValuationStructure.k0ToBCris p K b * x) =
      ValuationStructure.k0ToBCris p K b * (Galois.PeriodStructure.padicToBCris p a * x)
    ring

def bCrisToBdRK0Alg : Logarithm.PeriodRings.BCris p →ₐ[MaximalUnramified.K0 p K] Logarithm.PeriodRings.BdR p :=
  { ComparisonBd.bCrisToBdR p with commutes' := k0ToBCris_comparison p K }

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

instance tensorK0SMul : SMul (MaximalUnramified.K0 p K) (Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) := TensorProduct.leftHasSMul

instance tensorK0Module : Module (MaximalUnramified.K0 p K) (Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) := TensorProduct.leftModule

def dCrisK0Subtype (ρ : Representation ℚ_[p] K.fixingSubgroup V) :
    DcrisD.Dcris p K ρ →ₗ[MaximalUnramified.K0 p K] (Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) where
  toFun := Subtype.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tensorComparison_k0_smul (a : MaximalUnramified.K0 p K) (x : Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) :
    InvariantComparison.tensorComparison p (a • x) = a • InvariantComparison.tensorComparison p x :=
  tensorMap_smul (ComparisonScalars.bCrisToBdRAlg p).toLinearMap
    (fun a b => (bCrisToBdRK0Alg p K).toLinearMap.map_smul a b) a x

def dCrisToDeRhamTensor (ρ : Representation ℚ_[p] K.fixingSubgroup V) :
    DcrisD.Dcris p K ρ →ₗ[MaximalUnramified.K0 p K] (Logarithm.PeriodRings.BdR p ⊗[ℚ_[p]] V) where
  toFun x := InvariantComparison.tensorComparison p x.val
  map_add' x y := (InvariantComparison.tensorComparison p).map_add x.val y.val
  map_smul' a x := tensorComparison_k0_smul p K a x.val

theorem dCrisToDeRhamTensor_injective (ρ : Representation ℚ_[p] K.fixingSubgroup V) :
    Function.Injective (dCrisToDeRhamTensor p K ρ) :=
  (CrystallineEmbedding.tensorComparison_injective p).comp Subtype.val_injective

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonB
