import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Field.Equiv

/-! # Smooth Local Fiber -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SmoothLocalFiber.Constructions

noncomputable section

/-! A flat local map with a field as its closed fiber is formally smooth
when the residue characteristic is zero. This will apply to the parameter
map of the actual discrete valuation rings on the normalization. -/

open _root_.Algebra TensorProduct IsLocalRing

theorem formallySmooth_of_maximalIdeal_map
    (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Module.Flat R S] [Algebra.EssFiniteType R S]
    [PerfectField (ResidueField R)]
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    Algebra.FormallySmooth R S := by
  let e : ResidueField R ⊗[R] S ≃ₐ[R] S ⧸ maximalIdeal S :=
    ((Algebra.TensorProduct.comm R (ResidueField R) S).trans
      ((TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal R)).symm.restrictScalars R)).trans
        (Ideal.quotientEquivAlgOfEq R h)
  let : Field (S ⧸ maximalIdeal S) := Ideal.Quotient.field _
  have hf : IsField (S ⧸ maximalIdeal S) := Field.toIsField _
  let : Field (ResidueField R ⊗[R] S) :=
    (MulEquiv.isField hf e.toRingEquiv.toMulEquiv).toField
  let : Algebra.FormallySmooth (ResidueField R) (ResidueField R ⊗[R] S) := inferInstance
  let P := Algebra.EssFiniteType.subalgebra R S
  let : Algebra.FiniteType R P := inferInstanceAs
    (Algebra.FiniteType R (Algebra.EssFiniteType.subalgebra R S))
  let : Algebra.FinitePresentation R P :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
    (R := R) (S := S) (P := P) (Algebra.EssFiniteType.submonoid R S)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SmoothLocalFiber.Constructions
