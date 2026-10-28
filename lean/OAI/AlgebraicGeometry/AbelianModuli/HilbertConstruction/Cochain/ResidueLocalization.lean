import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ResidueExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangeTensorExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ScalarExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.TensorExactness
import Mathlib.RingTheory.Flat.Localization

/-! # Residue Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ResidueLocalization

noncomputable section

/-! Residue-field exactness of a finite free cochain model at a prime implies exactness over its localized coefficient ring, with the original R-linear tensor action. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits IsLocalRing
open scoped TensorProduct
universe u

theorem finiteFreeCochain_localization_exactAt_of_residue_exactAt
    {R : Type u} [CommRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hfree : ∀ q, Module.Free R (C.X q))
    (p : PrimeSpectrum R) (q : ℕ)
    (hres : (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex p.asIdeal.ResidueField C).ExactAt q) :
    (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex (Localization.AtPrime p.asIdeal) C).ExactAt q := by
  let A := Localization.AtPrime p.asIdeal
  let B := IsLocalRing.ResidueField A
  let S := C.sc q
  let T := HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R A S
  have : Module.Finite R S.X₁ := hfin ((ComplexShape.up ℕ).prev q)
  have : Module.Free R S.X₁ := hfree ((ComplexShape.up ℕ).prev q)
  have : Module.Finite R S.X₂ := hfin q
  have : Module.Free R S.X₂ := hfree q
  have : Module.Finite R S.X₃ := hfin ((ComplexShape.up ℕ).next q)
  have : Module.Free R S.X₃ := hfree ((ComplexShape.up ℕ).next q)
  have : Module.Finite A T.X₁ := inferInstanceAs (Module.Finite A (A ⊗[R] S.X₁))
  have : Module.Free A T.X₁ := inferInstanceAs (Module.Free A (A ⊗[R] S.X₁))
  have : Module.Finite A T.X₂ := inferInstanceAs (Module.Finite A (A ⊗[R] S.X₂))
  have : Module.Free A T.X₂ := inferInstanceAs (Module.Free A (A ⊗[R] S.X₂))
  have : Module.Finite A T.X₃ := inferInstanceAs (Module.Finite A (A ⊗[R] S.X₃))
  have : Module.Free A T.X₃ := inferInstanceAs (Module.Free A (A ⊗[R] S.X₃))
  have hnative : (S.map (ModuleCat.extendScalars (algebraMap R B))).Exact := by
    have h : (S.map (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor B)).Exact ↔
        (S.map (ModuleCat.extendScalars (algebraMap R B))).Exact := by
      have ht := Tensor.ScalarExactness.tensor_shortComplex_exact_iff_native (algebraMap R B) S
      rw [toAlgebra_algebraMap] at ht
      exact ht
    exact h.mp hres
  have hcomp : (S.map (ModuleCat.extendScalars
      ((algebraMap A B).comp (algebraMap R A)))).Exact := by
    rw [← IsScalarTower.algebraMap_eq R A B]
    exact hnative
  have hT : T.Exact := Local.ResidueExactness.LocalSectionLifting.finiteFreeShortComplex_exact_of_residue_exact T
    (Iterated.TensorExactness.iterated_tensor_exact_of_composite (A := A) S hcomp)
  exact (Base.ChangeTensorExactness.baseChange_shortComplex_exact_iff_tensor (B := A) S).mp hT

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ResidueLocalization
