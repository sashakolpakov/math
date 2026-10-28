import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.HomologySupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.FieldSupport
import Mathlib.RingTheory.LocalRing.Module

/-! # Flat Cochain Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatCochainSupport

noncomputable section

/-! Residue exactness detects localized exactness for finite flat cochain terms. This supplies cohomology support for finite projective models without choosing a global free basis. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits IsLocalRing
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R]

theorem finiteFlatCochain_localization_exactAt_of_residue_exactAt
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hflat : ∀ q, Module.Flat R (C.X q))
    (p : PrimeSpectrum R) (q : ℕ)
    (hres : (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex p.asIdeal.ResidueField C).ExactAt q) :
    (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex (Localization.AtPrime p.asIdeal) C).ExactAt q := by
  let A := Localization.AtPrime p.asIdeal
  let B := IsLocalRing.ResidueField A
  let S := C.sc q
  let T := HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R A S
  have : Module.Finite R S.X₁ := hfin ((ComplexShape.up ℕ).prev q)
  have : Module.Flat R S.X₁ := hflat ((ComplexShape.up ℕ).prev q)
  have : Module.Finite R S.X₂ := hfin q
  have : Module.Flat R S.X₂ := hflat q
  have : Module.Finite R S.X₃ := hfin ((ComplexShape.up ℕ).next q)
  have : Module.Flat R S.X₃ := hflat ((ComplexShape.up ℕ).next q)
  have : Module.Finite A T.X₁ := inferInstanceAs (Module.Finite A (A ⊗[R] S.X₁))
  have : Module.Flat A T.X₁ := inferInstanceAs (Module.Flat A (A ⊗[R] S.X₁))
  have : Module.Free A T.X₁ := Module.free_of_flat_of_isLocalRing
  have : Module.Finite A T.X₂ := inferInstanceAs (Module.Finite A (A ⊗[R] S.X₂))
  have : Module.Flat A T.X₂ := inferInstanceAs (Module.Flat A (A ⊗[R] S.X₂))
  have : Module.Free A T.X₂ := Module.free_of_flat_of_isLocalRing
  have : Module.Finite A T.X₃ := inferInstanceAs (Module.Finite A (A ⊗[R] S.X₃))
  have : Module.Flat A T.X₃ := inferInstanceAs (Module.Flat A (A ⊗[R] S.X₃))
  have : Module.Free A T.X₃ := Module.free_of_flat_of_isLocalRing
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

theorem finiteFlatCochain_homology_support_of_residue_exactAt
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hflat : ∀ q, Module.Flat R (C.X q))
    (I : Ideal R) (q : ℕ)
    (hres : ∀ p : PrimeSpectrum R, ¬ I ≤ p.asIdeal →
      (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex p.asIdeal.ResidueField C).ExactAt q) :
    Module.support R (C.homology q) ⊆ PrimeSpectrum.zeroLocus (I : Set R) :=
  Cochain.HomologySupport.cochain_homology_support_of_localization_exactAt C I q
    (fun p hp => finiteFlatCochain_localization_exactAt_of_residue_exactAt C hfin hflat p q (hres p hp))

theorem finiteFlatCochain_fieldSupport_homology_support
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hflat : ∀ q, Module.Flat R (C.X q))
    (I : Ideal R) (hfield : Cochain.FieldSupport.CochainFieldSupport C I) (q : ℕ) :
    Module.support R (C.homology q) ⊆ PrimeSpectrum.zeroLocus (I : Set R) := by
  apply finiteFlatCochain_homology_support_of_residue_exactAt C hfin hflat I q
  intro p hp
  apply hfield p.asIdeal.ResidueField
  simpa only [Ideal.ker_algebraMap_residueField] using hp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatCochainSupport
