import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FormSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothRelativeRank
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateRank
import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.PowerVanishing
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.AffineNeighborhood
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.EtaleCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover
import Mathlib.Topology.Sheaves.Stalks

/-! # Form Degree Bound -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.FormDegreeBound

noncomputable section

/-! The original differential-form sheaves of a smooth proper family
vanish above its actual relative dimension, over any commutative base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable (R : Type u) [CommRing R]
  (X : Over (Spec (CommRingCat.of R))) (g : ℕ) [SmoothOfRelativeDimension g X.hom]

theorem affine_sections (U : X.left.Opens) (hU : IsAffineOpen U)
    (σ : Type u) [Fintype σ] [LinearOrder σ]
    [Algebra (MvPolynomial σ R) (Intrinsic.SmoothClosedSections.ring R X U)]
    [IsScalarTower R (MvPolynomial σ R) (Intrinsic.SmoothClosedSections.ring R X U)]
    [Algebra.Etale (MvPolynomial σ R) (Intrinsic.SmoothClosedSections.ring R X U)]
    (p : PrimeSpectrum (Intrinsic.SmoothClosedSections.ring R X U)) (n : ℕ) (hn : g < n) :
    Subsingleton Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n, U) := by
  let b := IntegralComparison.Etale.CoordinateRank.basis R (Intrinsic.SmoothClosedSections.ring R X U) σ p g
    (Intrinsic.SmoothRelativeRank.sections R X g U hU p)
  let : Subsingleton (⋀[Intrinsic.SmoothClosedSections.ring R X U]^n (KaehlerDifferential R (Intrinsic.SmoothClosedSections.ring R X U))) :=
    Exterior.PowerVanishing.subsingleton b hn
  exact (IntegralComparison.Etale.FormSections.Integral.exteriorIso R X U hU σ n).injective.subsingleton

variable [IsProper X.hom]

theorem exists_zero_neighborhood (U : X.left.Opens) (x : X.left) (hx : x ∈ U)
    (n : ℕ) (hn : g < n) :
    ∃ V : X.left.Opens, V ≤ U ∧ x ∈ V ∧
      Subsingleton Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n, V) := by
  classical
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  obtain ⟨a, hxa⟩ := AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.covers R X x
  let C := AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateRing R X a
  let chart := AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap R X a
  obtain ⟨V, hV, hxV, hVU, hVC⟩ :=
    Closed.AffineNeighborhood.exists_subopen (𝟙 X.left) U chart.opensRange x hx hxa
  have hVC' : V ≤ chart.opensRange := hVC
  let σ := AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex R X a
  let : LinearOrder σ := linearOrderOfSTO WellOrderingRel
  let := AffineOpen.EtaleCoordinates.polynomialAlgebra R X V hV C chart hVC' σ
  let := AffineOpen.EtaleCoordinates.tower R X V hV C chart hVC' σ
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap_over R X a)
  let := AffineOpen.EtaleCoordinates.etale R X V hV C chart hVC' σ
  exact ⟨V, hVU, hxV, affine_sections R X g V hV σ (hV.primeIdealOf ⟨x, hxV⟩) n hn⟩

theorem sections_subsingleton (U : X.left.Opens) (n : ℕ) (hn : g < n) :
    Subsingleton Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n, U) := by
  constructor
  intro a b
  let F := (SheafOfModules.toSheaf X.left.ringCatSheaf).obj (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n)
  change (a : F.obj.obj (op U)) = b
  apply TopCat.Presheaf.IsSheaf.section_ext F.property
  intro x hx
  obtain ⟨V, hVU, hxV, hV⟩ := exists_zero_neighborhood R X g U x hx n hn
  exact ⟨V, hVU, hxV, @Subsingleton.elim _ hV _ _⟩

theorem sheaf_isZero (n : ℕ) (hn : g < n) :
    IsZero (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n) := by
  rw [IsZero.iff_id_eq_zero]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact @Subsingleton.elim _ (sections_subsingleton R X g U.unop n hn) _ _

theorem coefficient_sheaf_isZero (n : ℕ) (hn : g < n) :
    IsZero ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n) :=
  (GeometricComparison.Integral.FormsModules.IntegralFormsModules.coefficientSheafIso R X n).isZero_iff.mp
    ((AlgebraSheafScalars.functor R X).map_isZero (sheaf_isZero R X g n hn))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.FormDegreeBound
