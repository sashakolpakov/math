import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.CochainBicomplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatClosedPointCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ResidueScalarIso

/-! # Point Local Algebra Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.PointLocalAlgebraCohomology

noncomputable section

/-! The closed-point cohomology criterion works with any actual local algebra realizing the localization. All changes of local ring retain the coefficient action on the residue module. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits IsLocalRing
universe u
variable {R : Type u} [CommRing R]

def maximalQuotientLocalResidueIso
    (m : Ideal R) [m.IsMaximal] (B : Type u) [CommRing B] [IsLocalRing B]
    [Algebra R B] [IsLocalization m.primeCompl B] :
    ModuleCat.of R (R ⧸ m) ≅
      (ModuleCat.restrictScalars (algebraMap R B)).obj (ModuleCat.of B (ResidueField B)) := by
  let A := Localization.AtPrime m
  let e : A ≃ₐ[R] B := IsLocalization.algEquiv m.primeCompl A B
  let F := ModuleCat.restrictScalars (algebraMap R A)
  have h : algebraMap R B = e.toRingHom.comp (algebraMap R A) := by
    ext r
    exact (e.commutes r).symm
  exact (Closed.PointCochainLocalization.maximalQuotientResidueEquiv m).toLinearEquiv.toModuleIso ≪≫
    Closed.PointCochainLocalization.scalarTowerRestrictModuleIso (R := R) A m.ResidueField ≪≫
    F.mapIso (Local.ResidueScalarIso.localResidueRestrictionIso e.toRingEquiv) ≪≫
    (ModuleCat.restrictScalarsComp'App (algebraMap R A) e.toRingHom (algebraMap R B) h
      (ModuleCat.of B (ResidueField B))).symm

def singlePointSupportedCochainLocalAlgebraIso
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (m : Ideal R) [m.IsMaximal]
    (B : Type u) [CommRing B] [Algebra R B] [IsLocalization m.primeCompl B] (q : ℕ)
    [Module.Finite R (C.homology q)]
    (hs : Module.support R (C.homology q) ⊆ PrimeSpectrum.zeroLocus (m : Set R)) :
    C.homology q ≅ (ModuleCat.restrictScalars (algebraMap R B)).obj
      ((((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj C).homology q) := by
  let A := Localization.AtPrime m
  let e : A ≃ₐ[R] B := IsLocalization.algEquiv m.primeCompl A B
  let E := (Tensor.CochainBicomplex.tensorCochainFunctor C).mapIso e.toLinearEquiv.toModuleIso
  exact Closed.PointCochainLocalization.singlePointSupportedCochainLocalizationIso C m q hs ≪≫
    HomologicalComplex.homologyMapIso E q ≪≫ (Base.ChangeTensorHomology.baseChangeTensorHomologyIso (B := B) C q).symm

theorem finiteFlatCochain_cohomology_of_localAlgebra [IsNoetherianRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hflat : ∀ q, Module.Flat R (C.X q))
    (m : Ideal R) [m.IsMaximal] (hfield : Cochain.FieldSupport.CochainFieldSupport C m)
    (B : Type u) [CommRing B] [IsLocalRing B] [Algebra R B] [IsLocalization m.primeCompl B]
    (g : ℕ)
    (hvan : ∀ q, q ≠ g → IsZero
      ((((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj C).homology q))
    (etop : (((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj C).homology g ≅
      ModuleCat.of B (ResidueField B)) :
    (∀ q, q ≠ g → IsZero (C.homology q)) ∧ Nonempty (C.homology g ≅ ModuleCat.of R (R ⧸ m)) := by
  let F := ModuleCat.restrictScalars (algebraMap R B)
  have hf (q : ℕ) : Module.Finite R (C.homology q) := by
    have : Module.Finite R (C.X q) := hfin q
    exact Closed.PointCochainLocalization.finite_cochain_homology_of_finite_term C q
  have hs (q : ℕ) : Module.support R (C.homology q) ⊆ PrimeSpectrum.zeroLocus (m : Set R) :=
    HilbertConstruction.Finite.FlatCochainSupport.finiteFlatCochain_fieldSupport_homology_support C hfin hflat m hfield q
  constructor
  · intro q hq
    have : Module.Finite R (C.homology q) := hf q
    exact (F.map_isZero (hvan q hq)).of_iso (singlePointSupportedCochainLocalAlgebraIso C m B q (hs q))
  · have : Module.Finite R (C.homology g) := hf g
    exact ⟨singlePointSupportedCochainLocalAlgebraIso C m B g (hs g) ≪≫
      F.mapIso etop ≪≫ (maximalQuotientLocalResidueIso m B).symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.PointLocalAlgebraCohomology
