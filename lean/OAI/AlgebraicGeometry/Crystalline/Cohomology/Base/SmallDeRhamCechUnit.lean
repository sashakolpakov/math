import OAI.AlgebraicGeometry.Crystalline.Cohomology.NonemptyCechAdditive
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenOrdinaryFormUnit
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.EtaleSubchartCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation
import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationComplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TermwiseIso

/-! # Small De Rham Cech Unit -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCechUnit.BaseSmallDeRhamCechUnit

noncomputable section

/-! On the small coordinate cover the actual ordinary de Rham Cech total equals the sheafified total in all degrees. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]

local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens R X
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U

def unit : DeRhamGlobalId.DeRhamGlobal.presheafComplex R X ⟶ ProperDeRhamCechFiniteness.BaseSmoothProperDeRhamCechFiniteness.presheafComplex R X :=
  NumberTheory.PadicHodge.GeometricComparison.SheafificationComplex.SheafificationComplexUnit.unit (Opens.grothendieckTopology X.left) (DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

theorem forms (q : ℕ) (t : Fin (q + 1) → SmallEtaleCover.BaseSmallEtaleCover.Index R X) (n : ℕ) :
    IsIso (((unit R X).f n).app (op (∏ᶜ (U ∘ t)))) := by
  have hI : IsAffineOpen (∏ᶜ (U ∘ t)) := by
    rw [Affine.OpenFiniteProductPreservation.AffineOpenFiniteProductPreservation.product_iInf]
    exact IsAffineOpen.iInf (fun j => (SmallEtaleCover.BaseSmallEtaleCover.opens R X (t j)).property)
  let I : X.left.affineOpens := ⟨∏ᶜ (U ∘ t), hI⟩
  let i := SmallEtaleCover.BaseSmallEtaleCover.originalIndex R X (t 0)
  have hi : I.val ≤ ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens R X i := leOfHom (Pi.π (U ∘ t) 0)
  let σ := SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex R X i
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  let : Algebra (MvPolynomial σ R) (BaseAffine.OpenFormRegularity.BaseAffineOpenFormRegularity.ring R X I.val) :=
    EtaleSubchartCoordinates.BaseEtaleSubchartCoordinates.polynomialAlgebra R X I i hi
  let : IsScalarTower R (MvPolynomial σ R) (BaseAffine.OpenFormRegularity.BaseAffineOpenFormRegularity.ring R X I.val) :=
    EtaleSubchartCoordinates.BaseEtaleSubchartCoordinates.tower R X I i hi
  let : Algebra.Etale (MvPolynomial σ R) (BaseAffine.OpenFormRegularity.BaseAffineOpenFormRegularity.ring R X I.val) :=
    EtaleSubchartCoordinates.BaseEtaleSubchartCoordinates.etale R X I i hi
  exact BaseAffine.OpenOrdinaryFormUnit.BaseAffineOpenOrdinaryFormUnit.forms R X I.val I.property σ n

def bicomplex : HomologicalComplex₂ (ModuleCat.{u} R) (.up ℕ) (.up ℕ) :=
  ((NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor U).mapHomologicalComplex (.up ℕ)).obj
    (DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

def map : bicomplex R X ⟶ SmallDeRhamCech.BaseSmallDeRhamCech.bicomplex R X :=
  ((NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor U).mapHomologicalComplex (.up ℕ)).map (unit R X)

theorem row_isIso (n : ℕ) : IsIso ((BaseSmallDeRhamCechUnit.map R X).f n) :=
  NumberTheory.PadicHodge.GeometricComparison.Cech.TermwiseIso.CechTermwiseIso.isIso N ((unit R X).f n) (fun q t => forms R X q t n)

def iso : bicomplex R X ≅ SmallDeRhamCech.BaseSmallDeRhamCech.bicomplex R X := by
  let (n : ℕ) : IsIso ((BaseSmallDeRhamCechUnit.map R X).f n) := row_isIso R X n
  let : IsIso (BaseSmallDeRhamCechUnit.map R X) := HomologicalComplex.Hom.isIso_of_components _
  exact asIso (BaseSmallDeRhamCechUnit.map R X)

def totalIso : (bicomplex R X).total (.up ℕ) ≅ SmallDeRhamCech.BaseSmallDeRhamCech.total R X :=
  HomologicalComplex₂.total.mapIso (iso R X) (.up ℕ)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCechUnit.BaseSmallDeRhamCechUnit
