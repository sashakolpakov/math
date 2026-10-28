import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Terms
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.TotalAcyclic
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.TruncatedTotalAcyclic

/-! # Truncated Sections -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.TruncatedSections.IntrinsicCechHodgeComparison

noncomputable section

/-! The actual finite affine Čech comparison carries truncation images to every native Hodge filtration step. -/

open _root_.CategoryTheory Abelian _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
  {ι : Type} [Finite ι] (U : ι → X.left.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X
local instance : HasExt.{1} V := HasExt.standard _

def sections : CochainComplex (ModuleCat.{0} R) ℤ :=
  Terms.IntrinsicCechComparison.sections R X.left U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)

def equiv (n : ℕ) : (sections R X U).homology (n : ℤ) ≃ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X n :=
  Terms.IntrinsicCechComparison.equiv R X.left U hcover (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)
    (TotalAcyclic.IntrinsicCechTotalAcyclic.integerTotal_ext_subsingleton R X U hU) (n : ℤ)

def truncatedSections (r : ℤ) : CochainComplex (ModuleCat.{0} R) ℤ :=
  Terms.IntrinsicCechComparison.sections R X.left U (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r)

def truncatedEquiv (r : ℤ) (n : ℕ) :
    (truncatedSections R X U r).homology (n : ℤ) ≃ₗ[R]
      ((DerivedCategory.singleFunctor V 0).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) ⟶
        (DerivedCategory.Q.obj ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r).extend
          ComplexShape.embeddingUpNat))⟦(n : ℤ)⟧) :=
  Terms.IntrinsicCechComparison.equiv R X.left U hcover
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r)
    (TruncatedTotalAcyclic.IntrinsicCechTruncatedTotalAcyclic.integerTotal_ext_subsingleton R X U hU r) (n : ℤ)

def filtrationMap (n : ℕ) (r : ℤ) :
    (truncatedSections R X U r).homology (n : ℤ) →ₗ[R] (sections R X U).homology (n : ℤ) :=
  (HomologicalComplex.homologyMap
    (((Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left)).mapHomologicalComplex (.up ℤ)).map
      (Terms.IntrinsicCechComparison.totalMap R X.left U
        (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r))) (n : ℤ)).hom

theorem equiv_filtrationMap (n : ℕ) (r : ℤ)
    (a : (truncatedSections R X U r).homology (n : ℤ)) :
    equiv R X U hU hcover n (filtrationMap R X U n r a) =
      AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtrationMap R X n r (truncatedEquiv R X U hU hcover r n a) :=
  Terms.IntrinsicCechComparison.naturality R X.left U hcover
    (TruncatedTotalAcyclic.IntrinsicCechTruncatedTotalAcyclic.integerTotal_ext_subsingleton R X U hU r)
    (TotalAcyclic.IntrinsicCechTotalAcyclic.integerTotal_ext_subsingleton R X U hU)
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r) (n : ℤ) a

def filtration (n : ℕ) (r : ℤ) : Submodule R ((sections R X U).homology (n : ℤ)) :=
  LinearMap.range (filtrationMap R X U n r)

theorem equiv_filtration (n : ℕ) (r : ℤ) :
    (filtration R X U n r).map (equiv R X U hU hcover n).toLinearMap =
      AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration R X n r := by
  ext y
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨truncatedEquiv R X U hU hcover r n a, (equiv_filtrationMap R X U hU hcover n r a).symm⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := (truncatedEquiv R X U hU hcover r n).surjective a
    exact ⟨filtrationMap R X U n r b, ⟨b, rfl⟩, equiv_filtrationMap R X U hU hcover n r b⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.TruncatedSections.IntrinsicCechHodgeComparison
