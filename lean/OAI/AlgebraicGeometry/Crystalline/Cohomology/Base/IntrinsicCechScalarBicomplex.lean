import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicPresheafScalarComplex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.EtaleSubchartCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientChange
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.OpenBaseChangeNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TermwiseIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.TotalIso
import OAI.AlgebraicGeometry.SheafCohomology.Cech.Cochains
import Mathlib.CategoryTheory.Limits.Preserves.Lattice

/-! # Intrinsic Cech Scalar Bicomplex -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarBicomplex.BaseIntrinsicCechScalarBicomplex

noncomputable section

/-! Flat scalar extension of the actual finite affine Čech de Rham bicomplex. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace Simplicial

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)

section General
variable {ι : Type u} [Finite ι] (U : ι → X.left.Opens)

omit [Algebra R S] in
theorem opensFiniteLimits : PreservesFiniteLimits (Opens.map f.base) := by
  change PreservesFiniteLimits (OrderHom.ofClass f.base.frameHom).toFunctor
  infer_instance

local instance : PreservesFiniteLimits (Opens.map f.base) := opensFiniteLimits R S X Y f

theorem finiteIndices (n : SimplexCategory) : Finite ((FormalCoproduct.mk ι U).cech.obj (op n)).I := by
  change Finite (Fin (n.len + 1) → ι)
  infer_instance

local instance : (Cech.Descent.CechDescent.cechFunctor R X U).Additive := by
  change (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).Additive
  infer_instance

def source : HomologicalComplex₂ (ModuleCat.{u} S) (.up ℕ) (.up ℕ) :=
  Comparison.Betti.TotalComplexFunctor.mapBicomplex (NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S) (Cech.Descent.CechDescent.bicomplex R X U)

def middle : HomologicalComplex₂ (ModuleCat.{u} S) (.up ℕ) (.up ℕ) :=
  ((cechComplexFunctor U (A := ModuleCat.{u} S)).mapHomologicalComplex (.up ℕ)).obj
    (((IntrinsicPresheafScalarComplex.BaseIntrinsicPresheafScalarComplex.scalar R S X).mapHomologicalComplex (.up ℕ)).obj
      (DeRhamGlobalId.DeRhamGlobal.presheafComplex R X))

def inverseImage : HomologicalComplex₂ (ModuleCat.{u} S) (.up ℕ) (.up ℕ) :=
  ((cechComplexFunctor U (A := ModuleCat.{u} S)).mapHomologicalComplex (.up ℕ)).obj
    (((IntrinsicPresheafScalarComplex.BaseIntrinsicPresheafScalarComplex.preimage R S X Y f).mapHomologicalComplex (.up ℕ)).obj
      (DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y))

def coefficientIso : source R S X U ≅ middle R S X U :=
  (NatIso.mapHomologicalComplex
    (NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.iso (NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S)
      (FormalCoproduct.mk ι U).cech (finiteIndices R X U)) (.up ℕ)).app
        (DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

def map (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) :
    middle R S X U ⟶ inverseImage R S X Y f U :=
  ((cechComplexFunctor U (A := ModuleCat.{u} S)).mapHomologicalComplex (.up ℕ)).map
    (IntrinsicPresheafScalarComplex.BaseIntrinsicPresheafScalarComplex.map R S X Y f h)

def inverseImageIso : inverseImage R S X Y f U ≅
    Cech.Descent.CechDescent.bicomplex S Y (fun i => f ⁻¹ᵁ U i) :=
  (NatIso.mapHomologicalComplex (Cech.OpenBaseChangeNaturality.CechOpenBaseChangeNaturality.iso (Opens.map f.base) U)
    (.up ℕ)).app (DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y)

end General

variable [IsProper X.hom] [Smooth X.hom] [Module.Flat R S]
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))

local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens R X

local instance schemeSeparated : X.left.IsSeparated := by
  constructor
  rw [← terminal.comp_from X.hom]
  infer_instance

theorem chart_component_isIso (q : ℕ) (t : Fin (q + 1) → SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index R X)
    (n : ℕ) : IsIso (IntrinsicFormsScalarMap.BaseIntrinsicFormsScalarMap.component R S X Y f hp.w (∏ᶜ (U ∘ t)) n) := by
  have hI : IsAffineOpen (∏ᶜ (U ∘ t)) :=
    SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U (ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.affine R X) q t
  let I : X.left.affineOpens := ⟨∏ᶜ (U ∘ t), hI⟩
  let i := t 0
  have hi : I.val ≤ ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens R X i := leOfHom (Pi.π (U ∘ t) 0)
  let σ := SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex R X i
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  let : Algebra R Γ(X.left, I.val) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X I.val
  let : Algebra (MvPolynomial σ R) Γ(X.left, I.val) :=
    EtaleSubchartCoordinates.BaseEtaleSubchartCoordinates.polynomialAlgebra R X I i hi
  let : IsScalarTower R (MvPolynomial σ R) Γ(X.left, I.val) :=
    EtaleSubchartCoordinates.BaseEtaleSubchartCoordinates.tower R X I i hi
  let : Algebra.Etale (MvPolynomial σ R) Γ(X.left, I.val) :=
    EtaleSubchartCoordinates.BaseEtaleSubchartCoordinates.etale R X I i hi
  exact IntrinsicFormsScalarMap.BaseIntrinsicFormsScalarMap.component_isIso R S X Y f hp.w I.val σ hp I.property n

theorem row_isIso (n : ℕ) : IsIso ((BaseIntrinsicCechScalarBicomplex.map R S X Y f U hp.w).f n) :=
  NumberTheory.PadicHodge.GeometricComparison.Cech.TermwiseIso.CechTermwiseIso.isIso (FormalCoproduct.mk (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index R X) U).cech
    (IntrinsicFormsScalarMap.BaseIntrinsicFormsScalarMap.map R S X Y f hp.w n)
    (fun q t => chart_component_isIso R S X Y f hp q t n)

def iso : source R S X U ≅ Cech.Descent.CechDescent.bicomplex S Y (fun i => f ⁻¹ᵁ U i) := by
  let (n : ℕ) : IsIso ((BaseIntrinsicCechScalarBicomplex.map R S X Y f U hp.w).f n) := row_isIso R S X Y f hp n
  let : IsIso (BaseIntrinsicCechScalarBicomplex.map R S X Y f U hp.w) := HomologicalComplex.Hom.isIso_of_components _
  exact coefficientIso R S X U ≪≫ asIso (BaseIntrinsicCechScalarBicomplex.map R S X Y f U hp.w) ≪≫ inverseImageIso R S X Y f U

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarBicomplex.BaseIntrinsicCechScalarBicomplex
