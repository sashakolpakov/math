import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Tensor
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Flat

/-! # Etale Base Change -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.EtaleBaseChange.BundleCycles

noncomputable section

/-! Actual étale coefficient changes induce étale maps of deformation
algebras, by the proved base-change equivalence. -/

open scoped TensorProduct

variable {R : Type} [CommRing R] (I : Ideal R) (S : Type) [CommRing S] [Algebra R S]

def deformationBaseChangeRightEquiv [Module.Flat R S] :
    letI := (Maps.BundleCycles.deformationMap I (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map).toAlgebra
    Iff.BundleCycles.deformationAlgebra I ⊗[R] S ≃ₐ[Iff.BundleCycles.deformationAlgebra I] Iff.BundleCycles.deformationAlgebra (I.map (algebraMap R S)) := by
  let := (Maps.BundleCycles.deformationMap I (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map).toAlgebra
  refine { (Algebra.TensorProduct.comm R (Iff.BundleCycles.deformationAlgebra I) S).toRingEquiv.trans
      (Tensor.BundleCycles.deformationBaseChangeEquiv I S).toRingEquiv with commutes' := ?_ }
  intro a
  change Tensor.BundleCycles.deformationBaseChange I S (1 ⊗ₜ[R] a) =
    Maps.BundleCycles.deformationMap I (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map a
  rw [Tensor.BundleCycles.deformationBaseChange_tmul, one_smul]

theorem deformationMap_formallyEtale [Module.Flat R S] [Algebra.FormallyEtale R S] :
    letI := (Maps.BundleCycles.deformationMap I (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map).toAlgebra
    Algebra.FormallyEtale (Iff.BundleCycles.deformationAlgebra I) (Iff.BundleCycles.deformationAlgebra (I.map (algebraMap R S))) := by
  let := (Maps.BundleCycles.deformationMap I (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map).toAlgebra
  exact Algebra.FormallyEtale.of_equiv (R := Iff.BundleCycles.deformationAlgebra I)
    (A := Iff.BundleCycles.deformationAlgebra I ⊗[R] S) (B := Iff.BundleCycles.deformationAlgebra (I.map (algebraMap R S)))
    (deformationBaseChangeRightEquiv I S)

theorem deformationMap_etale [Algebra.Etale R S] :
    letI := (Maps.BundleCycles.deformationMap I (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map).toAlgebra
    Algebra.Etale (Iff.BundleCycles.deformationAlgebra I) (Iff.BundleCycles.deformationAlgebra (I.map (algebraMap R S))) := by
  let := (Maps.BundleCycles.deformationMap I (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map).toAlgebra
  exact Algebra.Etale.of_equiv (R := Iff.BundleCycles.deformationAlgebra I)
    (A := Iff.BundleCycles.deformationAlgebra I ⊗[R] S) (B := Iff.BundleCycles.deformationAlgebra (I.map (algebraMap R S)))
    (deformationBaseChangeRightEquiv I S)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.EtaleBaseChange.BundleCycles
