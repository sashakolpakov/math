import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatCochainSupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.PointCochainLocalization

/-! # Flat Closed Point Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatClosedPointCohomology

noncomputable section

/-! For a finite flat complex supported at a single closed point, local concentration and a single top residue module determine the complete cohomology on the affine base. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

theorem finiteFlatCochain_cohomology_of_closedPoint
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hflat : ∀ q, Module.Flat R (C.X q))
    (m : Ideal R) [m.IsMaximal] (hfield : Cochain.FieldSupport.CochainFieldSupport C m) (g : ℕ)
    (hvan : ∀ q, q ≠ g → IsZero
      ((((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R (Localization.AtPrime m)).mapHomologicalComplex
        (.up ℕ)).obj C).homology q))
    (etop : (((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R (Localization.AtPrime m)).mapHomologicalComplex
        (.up ℕ)).obj C).homology g ≅ ModuleCat.of (Localization.AtPrime m) m.ResidueField) :
    (∀ q, q ≠ g → IsZero (C.homology q)) ∧
      Nonempty (C.homology g ≅ ModuleCat.of R (R ⧸ m)) := by
  let A := Localization.AtPrime m
  let F := ModuleCat.restrictScalars (algebraMap R A)
  have hf (q : ℕ) : Module.Finite R (C.homology q) := by
    have : Module.Finite R (C.X q) := hfin q
    exact Closed.PointCochainLocalization.finite_cochain_homology_of_finite_term C q
  have hs (q : ℕ) : Module.support R (C.homology q) ⊆ PrimeSpectrum.zeroLocus (m : Set R) :=
    FlatCochainSupport.finiteFlatCochain_fieldSupport_homology_support C hfin hflat m hfield q
  constructor
  · intro q hq
    have : Module.Finite R (C.homology q) := hf q
    have hz : IsZero ((HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex A C).homology q) :=
      (F.map_isZero (hvan q hq)).of_iso (Base.ChangeTensorHomology.baseChangeTensorHomologyIso (B := A) C q).symm
    exact Closed.PointCochainLocalization.singlePointSupportedCochain_isZero_of_localization C m q (hs q) hz
  · have : Module.Finite R (C.homology g) := hf g
    exact ⟨Closed.PointCochainLocalization.singlePointSupportedCochainResidueIso C m g (hs g) etop⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatClosedPointCohomology
