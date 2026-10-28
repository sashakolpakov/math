import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicData
import Mathlib.Topology.Algebra.Module.Basic

/-! # Adelic Coefficient Topology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicCoefficientTopology

noncomputable section

/-! The specified finite-coefficient topology is the finite product
topology in its actual rational basis. Addition and scalar action are
continuous for that topology, and finite linear combinations are
continuous maps from the rational finite adeles. -/

open scoped TensorProduct _root_.Topology

variable (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]

def finiteCoefficientCoordinates : AdelicData.FiniteCoefficients E ≃ₗ[AdelicData.RationalFiniteAdeles]
    (Fin (Module.finrank ℚ E) → AdelicData.RationalFiniteAdeles) :=
  ((Module.finBasis ℚ E).baseChange AdelicData.RationalFiniteAdeles).equivFun

theorem finiteCoefficientCoordinates_continuous : Continuous (finiteCoefficientCoordinates E) :=
  continuous_induced_dom

instance finiteCoefficientTopologicalAddGroup : IsTopologicalAddGroup (AdelicData.FiniteCoefficients E) :=
  isTopologicalAddGroup_induced (finiteCoefficientCoordinates E).toAddEquiv

instance finiteCoefficientContinuousSMul : ContinuousSMul AdelicData.RationalFiniteAdeles (AdelicData.FiniteCoefficients E) :=
  continuousSMul_induced (finiteCoefficientCoordinates E)

variable {E}

theorem finite_adele_linear_combination_continuous {I : Type*} [Fintype I]
    (v : I → NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE (AdelicData.FiniteCoefficients E)) :
    Continuous (fun c : I → AdelicData.RationalFiniteAdeles => ∑ i, c i • v i) := by
  apply continuous_finsetSum
  intro i _
  exact (continuous_apply i).smul continuous_const

theorem finiteCoefficientLinearMap_continuous {W : Type*} [AddCommGroup W]
    [Module AdelicData.RationalFiniteAdeles W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    [ContinuousSMul AdelicData.RationalFiniteAdeles W] (f : AdelicData.FiniteCoefficients E →ₗ[AdelicData.RationalFiniteAdeles] W) :
    Continuous f := by
  let b := (Module.finBasis ℚ E).baseChange AdelicData.RationalFiniteAdeles
  have he : (fun x => ∑ i, b.equivFun x i • f (b i)) = f := by
    funext x
    exact (Finset.sum_congr rfl (fun i _ => (f.map_smul (b.equivFun x i) (b i)).symm)).trans
      ((map_sum f (fun i => b.equivFun x i • b i) Finset.univ).symm.trans
        (congrArg f (b.sum_equivFun x)))
  rw [← he]
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp (finiteCoefficientCoordinates_continuous E)).smul continuous_const

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicCoefficientTopology
