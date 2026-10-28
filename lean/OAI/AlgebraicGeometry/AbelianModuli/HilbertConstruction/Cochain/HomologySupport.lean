import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ResidueLocalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.ModuleTensorHomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ModuleSupportAnnihilation

/-! # Homology Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.HomologySupport

noncomputable section

/-! The homology of a finite free cochain model is supported where its residue-field cohomology can be nonzero. Localization and tensor comparison use the actual coefficient maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct
universe u

theorem cochain_homology_support_of_localization_exactAt
    {R : Type u} [CommRing R] (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (I : Ideal R) (q : ℕ)
    (hlocal : ∀ p : PrimeSpectrum R, ¬ I ≤ p.asIdeal →
      (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex (Localization.AtPrime p.asIdeal) C).ExactAt q) :
    Module.support R (C.homology q) ⊆ PrimeSpectrum.zeroLocus (I : Set R) := by
  intro p hp
  change I ≤ p.asIdeal
  by_contra hnot
  let A := Localization.AtPrime p.asIdeal
  have : Module.Flat R A := IsLocalization.flat A p.asIdeal.primeCompl
  have hz := (hlocal p hnot).isZero_homology
  have hTensor : Subsingleton (A ⊗[R] (C.homology q)) :=
    ModuleCat.subsingleton_of_isZero ((HilbertConstruction.Flat.ModuleTensorHomology.ModuleTensorFunctor.flatHomologyIso A C q).isZero_iff.mpr hz)
  let e : A ⊗[R] (C.homology q) ≃ₗ[A] LocalizedModule p.asIdeal.primeCompl (C.homology q) :=
    (LocalizedModule.isBaseChange p.asIdeal.primeCompl (C.homology q)).equiv
  have hloc : Subsingleton (LocalizedModule p.asIdeal.primeCompl (C.homology q)) :=
    ⟨fun x y => e.symm.injective (hTensor.elim _ _)⟩
  exact (Module.notMem_support_iff.mpr hloc) hp

theorem finiteFreeCochain_homology_support_of_residue_exactAt
    {R : Type u} [CommRing R] (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hfree : ∀ q, Module.Free R (C.X q))
    (I : Ideal R) (q : ℕ)
    (hres : ∀ p : PrimeSpectrum R, ¬ I ≤ p.asIdeal →
      (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex p.asIdeal.ResidueField C).ExactAt q) :
    Module.support R (C.homology q) ⊆ PrimeSpectrum.zeroLocus (I : Set R) :=
  cochain_homology_support_of_localization_exactAt C I q
    (fun p hp => ResidueLocalization.finiteFreeCochain_localization_exactAt_of_residue_exactAt C hfin hfree p q (hres p hp))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.HomologySupport
