import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.DeRhamOneCech
import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.Image

/-! # Sections -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.Sections.IntegralCechHodgeComparison

noncomputable section

/-! The actual integral three-term Čech comparison preserves every original Hodge image in degree one. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Module.Flat ℤ R]
  (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
  {ι : Type} [Finite ι] (U : ι → X.left.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)
local notation "A" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X

local instance : HasExt.{1} V := HasExt.standard _

abbrev sections := Integral.DeRhamOneCech.IntegralDeRhamHOneCech.sections R X U

abbrev equiv := Integral.DeRhamOneCech.IntegralDeRhamHOneCech.equiv R X U hU hcover

def truncatedSections (r : ℤ) : CochainComplex (ModuleCat.{0} R) ℤ :=
  IntrinsicCech.Terms.IntrinsicCechComparison.sections R X.left U (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r)

def truncatedEquiv (r : ℤ) : (truncatedSections R X U r).homology 1 ≃ₗ[R]
    FirstThree.Image.FirstThreeHodgeImage.hom A (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r) :=
  (IntrinsicCech.Terms.IntrinsicCechComparison.equiv R X.left U hcover (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r)
    (IntegralFirst.ThreeCechAcyclic.IntegralFirstThreeCechAcyclic.truncated_integerTotal_ext_subsingleton R X U hU r) 1).trans
      (FirstThree.Image.FirstThreeHodgeImage.hodgeProjectionEquiv R A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r).symm

def filtrationMap (r : ℤ) :
    (truncatedSections R X U r).homology 1 →ₗ[R] (sections R X U).homology 1 :=
  (HomologicalComplex.homologyMap
    (((Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left)).mapHomologicalComplex (.up ℤ)).map
      (IntrinsicCech.Terms.IntrinsicCechComparison.totalMap R X.left U (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r))) 1).hom

theorem equiv_filtrationMap (r : ℤ) (a : (truncatedSections R X U r).homology 1) :
    equiv R X U hU hcover (filtrationMap R X U r a) =
      AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtrationMap R X 1 r (truncatedEquiv R X U hU hcover r a) := by
  apply (Integral.DeRhamOneCech.IntegralDeRhamHOneCech.projectionEquiv R X).injective
  have hK : IntrinsicCech.Terms.IntrinsicCechComparison.AcyclicTerms R X.left U K :=
    IntegralFirst.ThreeCechAcyclic.IntegralFirstThreeCechAcyclic.integerTotal_ext_subsingleton R X U hU
  change (Integral.DeRhamOneCech.IntegralDeRhamHOneCech.projectionEquiv R X)
      ((Integral.DeRhamOneCech.IntegralDeRhamHOneCech.projectionEquiv R X).symm
        (IntrinsicCech.Terms.IntrinsicCechComparison.equiv R X.left U hcover K
          hK 1
            (filtrationMap R X U r a))) = _
  erw [LinearEquiv.apply_symm_apply]
  change _ = FirstThree.Image.FirstThreeHodgeImage.projectionEquiv R A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)
    (FirstThree.Image.FirstThreeHodgeImage.filtrationMap R A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r
      (truncatedEquiv R X U hU hcover r a))
  erw [FirstThree.Image.FirstThreeHodgeImage.projection_filtrationMap]
  erw [truncatedEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  exact IntrinsicCech.Terms.IntrinsicCechComparison.naturality R X.left U hcover
    (IntegralFirst.ThreeCechAcyclic.IntegralFirstThreeCechAcyclic.truncated_integerTotal_ext_subsingleton R X U hU r)
    (IntegralFirst.ThreeCechAcyclic.IntegralFirstThreeCechAcyclic.integerTotal_ext_subsingleton R X U hU)
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) 1 a

def filtration (r : ℤ) : Submodule R ((sections R X U).homology 1) :=
  LinearMap.range (filtrationMap R X U r)

theorem equiv_filtration (r : ℤ) :
    (filtration R X U r).map (equiv R X U hU hcover).toLinearMap = AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration R X 1 r := by
  ext y
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨truncatedEquiv R X U hU hcover r a, (equiv_filtrationMap R X U hU hcover r a).symm⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := (truncatedEquiv R X U hU hcover r).surjective a
    exact ⟨filtrationMap R X U r b, ⟨b, rfl⟩, equiv_filtrationMap R X U hU hcover r b⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.Sections.IntegralCechHodgeComparison
