import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicCoefficientTopology
import OAI.RepresentationTheory.Theta.AdelicTopology

/-! # Coefficient Topology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientTopology.TestTransport

noncomputable section

/-! Every rational basis gives the same topology on ReferenceFamily's actual
finite coefficient tensor algebra. Multiplication is continuous in it. -/

open scoped Classical TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicCoefficientTopology _root_.Module

variable (F : Type*) [Field F] [NumberField F]

def finiteCoefficientBasisHomeomorph {J : Type*} [Fintype J] (b : Basis J ℚ F) :
    AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F ≃ₜ (J → AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) where
  toEquiv := (b.baseChange AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles).equivFun.toEquiv
  continuous_toFun := AbelianModuli.ReferenceFamily.AdelicCoefficientTopology.finiteCoefficientLinearMap_continuous
    (b.baseChange AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles).equivFun.toLinearMap
  continuous_invFun := by
    change Continuous (b.baseChange AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles).equivFun.symm
    have hc : Continuous (fun x : J → AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles =>
        ∑ i, x i • (b.baseChange AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) i) :=
      continuous_finsetSum _ (fun i _ => (continuous_apply i).smul continuous_const)
    exact hc.congr (fun x => (Basis.equivFun_symm_apply _ x).symm)

theorem finiteCoefficientBasisHomeomorph_rational {J : Type*} [Fintype J]
    (b : Basis J ℚ F) (x : F) (i : J) :
    finiteCoefficientBasisHomeomorph F b (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding F x) i =
      algebraMap ℚ AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles (b.equivFun x i) := by
  change (b.baseChange AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles).repr (1 ⊗ₜ[ℚ] x) i = _
  rw [Basis.baseChange_repr_tmul]
  simp only [Algebra.smul_def, mul_one, Basis.equivFun_apply]

theorem finiteCoefficients_t2 : T2Space (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F) :=
  (finiteCoefficientBasisHomeomorph F (Module.finBasis ℚ F)).isEmbedding.t2Space

theorem finiteCoefficient_mul_continuous :
    Continuous (fun p : AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F × AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F => p.1 * p.2) := by
  let b := (Module.finBasis ℚ F).baseChange AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles
  have he (x y : AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F) : x * y =
      ∑ i, ∑ j, (b.equivFun x i * b.equivFun y j) • (b i * b j) := by
    conv_lhs => rw [← b.sum_equivFun x, ← b.sum_equivFun y]
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
    rw [Finset.sum_comm]
  have hc (i) : Continuous (fun x : AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F => b.equivFun x i) :=
    (continuous_apply i).comp (AbelianModuli.ReferenceFamily.AdelicCoefficientTopology.finiteCoefficientCoordinates_continuous F)
  have hcont : Continuous (fun p : AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F × AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients F =>
      ∑ i, ∑ j, (b.equivFun p.1 i * b.equivFun p.2 j) • (b i * b j)) := by
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact ((hc i).comp continuous_fst).mul ((hc j).comp continuous_snd) |>.smul continuous_const
  exact hcont.congr (fun p => (he p.1 p.2).symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientTopology.TestTransport
