import OAI.AlgebraicGeometry.Resolution.Blowups.CotangentAlgebraEquiv
import Mathlib.RingTheory.Ideal.CotangentBaseChange
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Flat Cotangent Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.FlatCotangentBaseChange.Construction

noncomputable section

/-! Flat base change of the conormal module for the actual extended ideal. -/

open scoped TensorProduct

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

def flatIdealCotangentEquiv (I : Ideal R) :
    S ⊗[R] I.Cotangent ≃ₗ[S] (I.map (algebraMap R S)).Cotangent := by
  let e := Algebra.TensorProduct.rid R S S
  let J := I.map (Algebra.TensorProduct.includeRight.toRingHom : R →+* S ⊗[R] R)
  have hJ : J.map e.toRingHom = I.map (algebraMap R S) := by
    rw [Ideal.map_map]
    apply congrArg (fun f : R →+* S => I.map f)
    apply RingHom.ext
    intro r
    change r • (1 : S) = algebraMap R S r
    rw [Algebra.smul_def, mul_one]
  exact (I.tensorCotangentEquiv R S).trans (CotangentAlgebraEquiv.Construction.idealCotangentAlgEquiv e J _ hJ)

theorem flatIdealCotangentEquiv_tmul (I : Ideal R) (s : S) (x : I) :
    flatIdealCotangentEquiv R S I (s ⊗ₜ[R] I.toCotangent x) =
      s • (I.map (algebraMap R S)).toCotangent ⟨algebraMap R S x.val, Ideal.mem_map_of_mem _ x.property⟩ := by
  rw [flatIdealCotangentEquiv, LinearEquiv.trans_apply, Ideal.tensorCotangentEquiv_tmul,
    map_smul, CotangentAlgebraEquiv.Construction.idealCotangentAlgEquiv_toCotangent]
  congr 1
  apply congrArg (I.map (algebraMap R S)).toCotangent
  apply Subtype.ext
  simp only [Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.FlatCotangentBaseChange.Construction
