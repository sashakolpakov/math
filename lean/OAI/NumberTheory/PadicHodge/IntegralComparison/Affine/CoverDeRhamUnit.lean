import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCechUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechComplex

/-! # Cover De Rham Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoverDeRhamUnit

noncomputable section

/-! Sheafification is an isomorphism on the actual de Rham Cech
bicomplex of any affine refinement of the smooth coordinate cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  {ι : Type u} (U : ι → X.left.affineOpens)
  (r : ι → AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index R X)
  (hr : ∀ i, (U i).val ≤ (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R X (r i)).val)

def opens : ι → X.left.Opens := fun i => (U i).val

local notation "V" => OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoverDeRhamUnit.opens R X U
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve V

include hr in
theorem forms (q : ℕ) (t : Fin (q + 1) → ι) (n : ℕ) :
    IsIso (((AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCechUnit.BaseSmallDeRhamCechUnit.unit R X).f n).app (op (∏ᶜ (V ∘ t)))) := by
  have hI : IsAffineOpen (∏ᶜ (V ∘ t)) := by
    rw [AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation.AffineOpenFiniteProductPreservation.product_iInf]
    exact IsAffineOpen.iInf (fun j => (U (t j)).property)
  let I : X.left.affineOpens := ⟨∏ᶜ (V ∘ t), hI⟩
  let i := AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.originalIndex R X (r (t 0))
  have hi : I.val ≤ AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens R X i :=
    (leOfHom (Pi.π (V ∘ t) 0)).trans (hr (t 0))
  let σ := AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex R X i
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  let : Algebra (MvPolynomial σ R) (AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenFormRegularity.BaseAffineOpenFormRegularity.ring R X I.val) :=
    AlgebraicGeometry.Crystalline.Cohomology.Base.EtaleSubchartCoordinates.BaseEtaleSubchartCoordinates.polynomialAlgebra R X I i hi
  let : IsScalarTower R (MvPolynomial σ R) (AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenFormRegularity.BaseAffineOpenFormRegularity.ring R X I.val) :=
    AlgebraicGeometry.Crystalline.Cohomology.Base.EtaleSubchartCoordinates.BaseEtaleSubchartCoordinates.tower R X I i hi
  let : Algebra.Etale (MvPolynomial σ R) (AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenFormRegularity.BaseAffineOpenFormRegularity.ring R X I.val) :=
    AlgebraicGeometry.Crystalline.Cohomology.Base.EtaleSubchartCoordinates.BaseEtaleSubchartCoordinates.etale R X I i hi
  exact AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenOrdinaryFormUnit.BaseAffineOpenOrdinaryFormUnit.forms R X I.val I.property σ n

def bicomplex : HomologicalComplex₂ (ModuleCat.{u} R) (.up ℕ) (.up ℕ) :=
  ((NonemptyCechNerve.complexFunctor V).mapHomologicalComplex (.up ℕ)).obj
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

def map : bicomplex R X U ⟶ IntrinsicDeRham.CechComplex.Intrinsic.bicomplex R X V :=
  ((NonemptyCechNerve.complexFunctor V).mapHomologicalComplex (.up ℕ)).map
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCechUnit.BaseSmallDeRhamCechUnit.unit R X)

include hr in
theorem row_isIso (n : ℕ) : IsIso ((CoverDeRhamUnit.map R X U).f n) :=
  GeometricComparison.Cech.TermwiseIso.CechTermwiseIso.isIso N ((AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCechUnit.BaseSmallDeRhamCechUnit.unit R X).f n)
    (fun q t => forms R X U r hr q t n)

def iso : bicomplex R X U ≅ IntrinsicDeRham.CechComplex.Intrinsic.bicomplex R X V := by
  let (n : ℕ) : IsIso ((CoverDeRhamUnit.map R X U).f n) := row_isIso R X U r hr n
  let : IsIso (CoverDeRhamUnit.map R X U) := HomologicalComplex.Hom.isIso_of_components _
  exact asIso (CoverDeRhamUnit.map R X U)

def totalIso : (bicomplex R X U).total (.up ℕ) ≅ IntrinsicDeRham.CechComplex.Intrinsic.total R X V :=
  HomologicalComplex₂.total.mapIso (iso R X U r hr) (.up ℕ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoverDeRhamUnit
