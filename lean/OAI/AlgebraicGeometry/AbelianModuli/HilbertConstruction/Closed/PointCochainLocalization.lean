import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.PointModuleLocalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangeTensorHomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.ModuleTensorHomology
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Point Cochain Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.PointCochainLocalization

noncomputable section

/-! A finite cochain homology module supported at one closed point is recovered from the cohomology of the localized complex. In particular, a localized single residue module gives the actual quotient module on the affine base. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R]

theorem finite_cochain_homology_of_finite_term [IsNoetherianRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) [Module.Finite R (C.X q)] :
    Module.Finite R (C.homology q) := by
  let S := C.sc q
  have : Module.Finite R S.X₂ := inferInstanceAs (Module.Finite R (C.X q))
  have : Module.Finite R S.g.hom.ker := inferInstance
  have : Module.Finite R S.moduleCatLeftHomologyData.H :=
    inferInstanceAs (Module.Finite R (S.g.hom.ker ⧸ LinearMap.range S.moduleCatToCycles))
  exact Module.Finite.equiv S.moduleCatHomologyIso.symm.toLinearEquiv

def singlePointSupportedCochainLocalizationIso
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (m : Ideal R) [m.IsMaximal] (q : ℕ)
    [Module.Finite R (C.homology q)]
    (hs : Module.support R (C.homology q) ⊆ PrimeSpectrum.zeroLocus (m : Set R)) :
    C.homology q ≅ (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex (Localization.AtPrime m) C).homology q := by
  let A := Localization.AtPrime m
  have : Module.Flat R A := IsLocalization.flat A m.primeCompl
  let E : A ⊗[R] (C.homology q) ≃ₗ[A] LocalizedModule m.primeCompl (C.homology q) :=
    (LocalizedModule.isBaseChange m.primeCompl (C.homology q)).equiv
  exact (Single.PointModuleLocalization.singlePointSupportedLocalizationEquiv m hs).toModuleIso ≪≫
    (E.restrictScalars R).symm.toModuleIso ≪≫ HilbertConstruction.Flat.ModuleTensorHomology.ModuleTensorFunctor.flatHomologyIso A C q

theorem singlePointSupportedCochain_isZero_of_localization
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (m : Ideal R) [m.IsMaximal] (q : ℕ)
    [Module.Finite R (C.homology q)]
    (hs : Module.support R (C.homology q) ⊆ PrimeSpectrum.zeroLocus (m : Set R))
    (hz : IsZero ((HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex (Localization.AtPrime m) C).homology q)) :
    IsZero (C.homology q) := hz.of_iso (singlePointSupportedCochainLocalizationIso C m q hs)

def scalarTowerRestrictModuleIso
    (A M : Type u) [CommRing A] [Algebra R A] [AddCommGroup M]
    [Module A M] [Module R M] [IsScalarTower R A M] :
    ModuleCat.of R M ≅ (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A M) := by
  let e : M ≃ₗ[R] ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A M)) := {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun r x => by
      change r • x = algebraMap R A r • x
      exact (IsScalarTower.algebraMap_smul A r x).symm }
  exact e.toModuleIso

def maximalQuotientResidueEquiv (m : Ideal R) [m.IsMaximal] :
    (R ⧸ m) ≃ₐ[R] m.ResidueField :=
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ m) m.ResidueField)
    m.bijective_algebraMap_quotient_residueField

def singlePointSupportedCochainResidueIso
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (m : Ideal R) [m.IsMaximal] (q : ℕ)
    [Module.Finite R (C.homology q)]
    (hs : Module.support R (C.homology q) ⊆ PrimeSpectrum.zeroLocus (m : Set R))
    (e : (((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R (Localization.AtPrime m)).mapHomologicalComplex
        (.up ℕ)).obj C).homology q ≅ ModuleCat.of (Localization.AtPrime m) m.ResidueField) :
    C.homology q ≅ ModuleCat.of R (R ⧸ m) :=
  singlePointSupportedCochainLocalizationIso C m q hs ≪≫
    (Base.ChangeTensorHomology.baseChangeTensorHomologyIso (B := Localization.AtPrime m) C q).symm ≪≫
    (ModuleCat.restrictScalars (algebraMap R (Localization.AtPrime m))).mapIso e ≪≫
    (scalarTowerRestrictModuleIso (R := R) (Localization.AtPrime m) m.ResidueField).symm ≪≫
    (maximalQuotientResidueEquiv m).symm.toLinearEquiv.toModuleIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.PointCochainLocalization
