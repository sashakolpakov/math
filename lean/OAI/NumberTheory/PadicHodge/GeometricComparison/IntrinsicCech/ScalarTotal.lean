import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarBicomplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Scalar Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarTotal.IntrinsicCechScalarTotal

noncomputable section

/-! Flat scalar extension commutes with the actual total Čech de Rham complex and its cohomology. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left) {ι : Type} [Finite ι] (U : ι → X.left.Opens)

def complex : CochainComplex (ModuleCat.{0} R) ℤ :=
  ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex R X U).total (.up ℕ)).extend ComplexShape.embeddingUpNat

variable [Algebra ℚ R] [Algebra ℚ S] [Module.Flat R S] [IsSeparated X.hom]
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (hU : ∀ i, IsAffineOpen (U i))

def iso : ((FlatScalar.FlatScalarExtension.moduleFunctor R S).mapHomologicalComplex (.up ℤ)).obj
    (complex R X U) ≅ complex S Y (fun i => f ⁻¹ᵁ U i) :=
  (GeometricComparison.Finite.TotalIso.FiniteTotalExtension.iso (FlatScalar.FlatScalarExtension.moduleFunctor R S) (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex R X U)).symm ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{0} S)).mapIso
      (HomologicalComplex₂.total.mapIso (ScalarBicomplex.IntrinsicCechScalarBicomplex.iso R S X Y f U hp hU) (.up ℕ))

def cohomologyEquiv (n : ℤ) : S ⊗[R] (complex R X U).homology n ≃ₗ[S]
    (complex S Y (fun i => f ⁻¹ᵁ U i)).homology n :=
  (ExactHomology.ExactHomologyComparison.iso (FlatScalar.FlatScalarExtension.moduleFunctor R S) (.up ℤ)
    (complex R X U) (complex S Y (fun i => f ⁻¹ᵁ U i)) (iso R S X Y f U hp hU) n).toLinearEquiv

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarTotal.IntrinsicCechScalarTotal
