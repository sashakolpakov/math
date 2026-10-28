import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.PresheafScalarComplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.OpenBaseChangeNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TermwiseIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.TotalIso
import OAI.AlgebraicGeometry.SheafCohomology.Cech.Cochains
import Mathlib.CategoryTheory.Limits.Preserves.Lattice

/-! # Scalar Bicomplex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarBicomplex.IntrinsicCechScalarBicomplex

noncomputable section

/-! Flat scalar extension of the actual finite affine Čech de Rham bicomplex. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace Simplicial

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left) {ι : Type} [Finite ι] (U : ι → X.left.Opens)

omit [Algebra R S] in
theorem opensFiniteLimits : PreservesFiniteLimits (Opens.map f.base) := by
  change PreservesFiniteLimits (OrderHom.ofClass f.base.frameHom).toFunctor
  infer_instance

local instance : PreservesFiniteLimits (Opens.map f.base) := opensFiniteLimits R S X Y f

theorem finiteIndices (n : SimplexCategory) : Finite ((FormalCoproduct.mk ι U).cech.obj (op n)).I := by
  change Finite (Fin (n.len + 1) → ι)
  infer_instance

local instance : (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).Additive := by
  change (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).Additive
  infer_instance

def source : HomologicalComplex₂ (ModuleCat.{0} S) (.up ℕ) (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex (FlatScalar.FlatScalarExtension.moduleFunctor R S) (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex R X U)

def middle : HomologicalComplex₂ (ModuleCat.{0} S) (.up ℕ) (.up ℕ) :=
  ((cechComplexFunctor U (A := ModuleCat.{0} S)).mapHomologicalComplex (.up ℕ)).obj
    (((Intrinsic.PresheafScalarComplex.IntrinsicPresheafScalarComplex.scalar R S X).mapHomologicalComplex (.up ℕ)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X))

def inverseImage : HomologicalComplex₂ (ModuleCat.{0} S) (.up ℕ) (.up ℕ) :=
  ((cechComplexFunctor U (A := ModuleCat.{0} S)).mapHomologicalComplex (.up ℕ)).obj
    (((Intrinsic.PresheafScalarComplex.IntrinsicPresheafScalarComplex.preimage R S X Y f).mapHomologicalComplex (.up ℕ)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y))

def coefficientIso : source R S X U ≅ middle R S X U :=
  (NatIso.mapHomologicalComplex
    (GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.iso (FlatScalar.FlatScalarExtension.moduleFunctor R S)
      (FormalCoproduct.mk ι U).cech (finiteIndices R X U)) (.up ℕ)).app
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

def map (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) :
    middle R S X U ⟶ inverseImage R S X Y f U :=
  ((cechComplexFunctor U (A := ModuleCat.{0} S)).mapHomologicalComplex (.up ℕ)).map
    (Intrinsic.PresheafScalarComplex.IntrinsicPresheafScalarComplex.map R S X Y f h)

def inverseImageIso : inverseImage R S X Y f U ≅
    AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex S Y (fun i => f ⁻¹ᵁ U i) :=
  (NatIso.mapHomologicalComplex (Cech.OpenBaseChangeNaturality.CechOpenBaseChangeNaturality.iso (Opens.map f.base) U)
    (.up ℕ)).app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y)

omit [Finite ι] in
theorem row_isIso [Algebra ℚ R] [Algebra ℚ S] [Module.Flat R S] [IsSeparated X.hom]
    (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (hU : ∀ i, IsAffineOpen (U i)) (q : ℕ) : IsIso ((IntrinsicCechScalarBicomplex.map R S X Y f U hp.w).f q) := by
  have : X.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from X.hom]
    infer_instance
  apply Cech.TermwiseIso.CechTermwiseIso.isIso (FormalCoproduct.mk ι U).cech (Intrinsic.FormsScalarMap.IntrinsicFormsScalarMap.map R S X Y f hp.w q)
  intro p t
  exact Intrinsic.FormsScalarMap.IntrinsicFormsScalarMap.component_isIso R S X Y f hp.w hp (∏ᶜ (U ∘ t))
    (AlgebraicGeometry.SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U hU p t) q

def iso [Algebra ℚ R] [Algebra ℚ S] [Module.Flat R S] [IsSeparated X.hom]
    (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (hU : ∀ i, IsAffineOpen (U i)) :
    source R S X U ≅ AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex S Y (fun i => f ⁻¹ᵁ U i) := by
  have (q : ℕ) : IsIso ((IntrinsicCechScalarBicomplex.map R S X Y f U hp.w).f q) := row_isIso R S X Y f U hp hU q
  have : IsIso (IntrinsicCechScalarBicomplex.map R S X Y f U hp.w) := HomologicalComplex.Hom.isIso_of_components _
  exact coefficientIso R S X U ≪≫ asIso (IntrinsicCechScalarBicomplex.map R S X Y f U hp.w) ≪≫ inverseImageIso R S X Y f U

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarBicomplex.IntrinsicCechScalarBicomplex
