import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreePresheafScalarComplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.CechCoordinateUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.OpenBaseChangeNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TermwiseIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.TotalIso
import OAI.AlgebraicGeometry.SheafCohomology.Cech.Cochains
import Mathlib.CategoryTheory.Limits.Preserves.Lattice

/-! # Three Cech Scalar Bicomplex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechScalarBicomplex.IntegralFirstThreeCechScalarBicomplex

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
  AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex (FlatScalar.FlatScalarExtension.moduleFunctor R S) (IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R X U)

def middle : HomologicalComplex₂ (ModuleCat.{0} S) (.up ℕ) (.up ℕ) :=
  ((cechComplexFunctor U (A := ModuleCat.{0} S)).mapHomologicalComplex (.up ℕ)).obj
    (((Intrinsic.PresheafScalarComplex.IntrinsicPresheafScalarComplex.scalar R S X).mapHomologicalComplex (.up ℕ)).obj
      (FirstThree.ThreeComplex.FirstThreeComplex.complex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)))

def inverseImage : HomologicalComplex₂ (ModuleCat.{0} S) (.up ℕ) (.up ℕ) :=
  ((cechComplexFunctor U (A := ModuleCat.{0} S)).mapHomologicalComplex (.up ℕ)).obj
    (((Intrinsic.PresheafScalarComplex.IntrinsicPresheafScalarComplex.preimage R S X Y f).mapHomologicalComplex (.up ℕ)).obj
      (FirstThree.ThreeComplex.FirstThreeComplex.complex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y)))

def coefficientIso : source R S X U ≅ middle R S X U :=
  (NatIso.mapHomologicalComplex
    (GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.iso (FlatScalar.FlatScalarExtension.moduleFunctor R S)
      (FormalCoproduct.mk ι U).cech (finiteIndices R X U)) (.up ℕ)).app
        (FirstThree.ThreeComplex.FirstThreeComplex.complex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X))

def map (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) :
    middle R S X U ⟶ inverseImage R S X Y f U :=
  ((cechComplexFunctor U (A := ModuleCat.{0} S)).mapHomologicalComplex (.up ℕ)).map
    (ThreePresheafScalarComplex.IntegralFirstThreePresheafScalarComplex.map R S X Y f h)

def inverseImageIso : inverseImage R S X Y f U ≅
    IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex S Y (fun i => f ⁻¹ᵁ U i) :=
  (NatIso.mapHomologicalComplex (Cech.OpenBaseChangeNaturality.CechOpenBaseChangeNaturality.iso (Opens.map f.base) U)
    (.up ℕ)).app (FirstThree.ThreeComplex.FirstThreeComplex.complex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y))

omit [Finite ι] in
theorem ordinary_row_isIso [Module.Flat R S] [IsSeparated X.hom]
    (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (hU : ∀ i, IsAffineOpen (U i)) (q : ℕ) (hq : q ≤ 2) :
    IsIso ((cechComplexFunctor U (A := ModuleCat.{0} S)).map (Intrinsic.FormsScalarMap.IntrinsicFormsScalarMap.map R S X Y f hp.w q)) := by
  have : X.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from X.hom]
    infer_instance
  apply Cech.TermwiseIso.CechTermwiseIso.isIso (FormalCoproduct.mk ι U).cech (Intrinsic.FormsScalarMap.IntrinsicFormsScalarMap.map R S X Y f hp.w q)
  intro p t
  exact Integral.IntrinsicFormsScalarIso.IntegralIntrinsicFormsScalarIso.component_isIso R S X Y f hp.w hp (∏ᶜ (U ∘ t))
    (AlgebraicGeometry.SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U hU p t) q hq

omit [Finite ι] in
theorem row_isIso [Module.Flat R S] [IsSeparated X.hom]
    (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (hU : ∀ i, IsAffineOpen (U i)) (q : ℕ) : IsIso ((IntegralFirstThreeCechScalarBicomplex.map R S X Y f U hp.w).f q) := by
  rcases q with _ | (_ | (_ | q))
  · exact ordinary_row_isIso R S X Y f U hp hU 0 (by omega)
  · exact ordinary_row_isIso R S X Y f U hp hU 1 (by omega)
  · exact ordinary_row_isIso R S X Y f U hp hU 2 (by omega)
  · let : IsIso ((ThreePresheafScalarComplex.IntegralFirstThreePresheafScalarComplex.map R S X Y f hp.w).f (q + 3)) :=
      ThreePresheafScalarComplex.IntegralFirstThreePresheafScalarComplex.high_isIso R S X Y f hp.w q
    exact (cechComplexFunctor U (A := ModuleCat.{0} S)).map_isIso
      ((ThreePresheafScalarComplex.IntegralFirstThreePresheafScalarComplex.map R S X Y f hp.w).f (q + 3))

def iso [Module.Flat R S] [IsSeparated X.hom]
    (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (hU : ∀ i, IsAffineOpen (U i)) :
    source R S X U ≅ IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex S Y (fun i => f ⁻¹ᵁ U i) := by
  have (q : ℕ) : IsIso ((IntegralFirstThreeCechScalarBicomplex.map R S X Y f U hp.w).f q) := row_isIso R S X Y f U hp hU q
  have : IsIso (IntegralFirstThreeCechScalarBicomplex.map R S X Y f U hp.w) := HomologicalComplex.Hom.isIso_of_components _
  exact coefficientIso R S X U ≪≫ asIso (IntegralFirstThreeCechScalarBicomplex.map R S X Y f U hp.w) ≪≫ inverseImageIso R S X Y f U

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechScalarBicomplex.IntegralFirstThreeCechScalarBicomplex
