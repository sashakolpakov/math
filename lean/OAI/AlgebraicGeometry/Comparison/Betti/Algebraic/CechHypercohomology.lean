import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CechAcyclicTerms
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveConstantSections
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.AffineCover

/-! # Cech Hypercohomology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CechHypercohomology

noncomputable section

/-! A finite affine Čech–de Rham resolution computes the original algebraic hypercohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [IsSeparated X.hom]
  {ι : Type} [Finite ι] (U : ι → X.left.Opens)

local instance : HasExt.{1} (HypercohomologyForget.AdditiveZariskiSheaves X) := HasExt.standard _
local instance : HasDerivedCategory.{1} (HypercohomologyForget.AdditiveZariskiSheaves X) := HasDerivedCategory.standard _

def algebraicCechGlobalSectionsComplex : CochainComplex AddCommGrpCat.{0} ℤ :=
  AdditiveConstantSections.Cech.additiveGlobalSectionsComplex (TopCat.of X.left) (CechResolution.algebraicCechTotalComplexInt X U)

def finiteAffine_algebraicCechHypercohomologyEquiv
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : ⨆ i, U i = ⊤) (n : ℕ) :
    (algebraicCechGlobalSectionsComplex X U).homology (n : ℤ) ≃+ Sheaves.algebraicDeRham X n := by
  let K := CechResolution.algebraicCechTotalComplexInt X U
  have : K.IsStrictlyGE 0 := CechResolution.algebraicCechTotalComplexInt_nonnegative X U
  let A : HypercohomologyForget.AdditiveZariskiSheaves X := AdditiveConstantExt.Cech.constantIntegers (TopCat.of X.left)
  let e₁ := ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) (n : ℤ)).mapIso
    (AdditiveConstantSections.Cech.constantIntegerHomSectionsComplexIso (TopCat.of X.left) K).symm).addCommGroupIsoToAddEquiv
  let e₂ := Acyclic.HomDerived.Ext.acyclicHomCohomologyDerivedEquiv A K 0
    (CechAcyclicTerms.algebraicCechTotalComplexInt_termExt_acyclic X U hU) (n : ℤ)
  have : QuasiIso (CechResolution.algebraicCechResolutionMap X U) := CechResolution.algebraicCechResolutionMap_quasiIso X U hcover
  let r := DerivedCategory.Q.map (CechResolution.algebraicCechResolutionMap X U)
  have : IsIso r := (DerivedCategory.isIso_Q_map_iff_quasiIso (HypercohomologyForget.AdditiveZariskiSheaves X) _).mpr
    (CechResolution.algebraicCechResolutionMap_quasiIso X U hcover)
  let e₃ := (Linear.homCongr ℤ
    (Iso.refl ((DerivedCategory.singleFunctor (HypercohomologyForget.AdditiveZariskiSheaves X) 0).obj A))
    ((shiftFunctor (DerivedCategory (HypercohomologyForget.AdditiveZariskiSheaves X)) (n : ℤ)).mapIso (asIso r)).symm).toAddEquiv
  exact e₁.trans (e₂.trans (e₃.trans (HypercohomologyForget.algebraicHypercohomologyForgetEquiv X n).symm))

def smooth_algebraicHypercohomologyCechResolutionEquiv [QuasiCompact X.hom] (n : ℕ) :
    (algebraicCechGlobalSectionsComplex X (Betti.Finite.AffineCover.finiteAlgebraicAffineOpens X)).homology (n : ℤ) ≃+
      Sheaves.algebraicDeRham X n :=
  finiteAffine_algebraicCechHypercohomologyEquiv X (Betti.Finite.AffineCover.finiteAlgebraicAffineOpens X)
    (Betti.Finite.AffineCover.finiteAlgebraicAffineOpens_affine X) (Betti.Finite.AffineCover.finiteAlgebraicAffineOpens_cover X) n

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CechHypercohomology
