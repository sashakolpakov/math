import OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenFormRegularity
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ProperDeRhamCechFiniteness
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalRegularity
import OAI.AlgebraicGeometry.SheafCohomology.Cech.Cochains

/-! # Smooth Proper Cech Regularity -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperCechRegularity.BaseSmoothProperCechRegularity

noncomputable section

/-! # The original smooth proper de Rham Cech total is termwise regular over its base -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  [IsProper X.hom] [Smooth X.hom]

local notation "I" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index R X
local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens R X

theorem affine_subopen (i : I) (W : X.left.Opens) (hW : IsAffineOpen W) (h : W ≤ U i)
    (n : ℕ) (r : R) (hr : r ∈ nonZeroDivisors R) :
    IsSMulRegular (((DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n).obj.obj (op W)) r := by
  let C := SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateRing R X i
  let σ := SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex R X i
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  let : Algebra R C := SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateAlgebra R X i
  let : Algebra (MvPolynomial σ R) C := SmoothProperEtaleCover.BaseSmoothProperEtaleCover.polynomialAlgebra R X i
  let : Algebra.Etale (MvPolynomial σ R) C := SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateEtale R X i
  let : IsScalarTower R (MvPolynomial σ R) C := SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateTower R X i
  let g : Spec (CommRingCat.of C) ⟶ X.left := SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap R X i
  let : IsOpenImmersion g := SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap_open R X i
  let : Algebra (MvPolynomial σ R) (BaseAffine.OpenFormRegularity.BaseAffineOpenFormRegularity.ring R X W) :=
    NumberTheory.PadicHodge.IntegralComparison.AffineOpen.EtaleCoordinates.polynomialAlgebra R X W hW C g h σ
  let : Algebra.Etale (MvPolynomial σ R) (BaseAffine.OpenFormRegularity.BaseAffineOpenFormRegularity.ring R X W) :=
    NumberTheory.PadicHodge.IntegralComparison.AffineOpen.EtaleCoordinates.etale R X W hW C g h σ
  let : IsScalarTower R (MvPolynomial σ R) (BaseAffine.OpenFormRegularity.BaseAffineOpenFormRegularity.ring R X W) :=
    NumberTheory.PadicHodge.IntegralComparison.AffineOpen.EtaleCoordinates.tower R X W hW C g h σ
      (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap_over R X i)
  exact BaseAffine.OpenFormRegularity.BaseAffineOpenFormRegularity.regular R X W hW σ n r hr

theorem intersection (n p : ℕ) (t : Fin (p + 1) → I) (r : R) (hr : r ∈ nonZeroDivisors R) :
    IsSMulRegular (((DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n).obj.obj (op (∏ᶜ (U ∘ t)))) r := by
  let : X.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from X.hom]
    infer_instance
  exact affine_subopen R X (t 0) (∏ᶜ (U ∘ t))
    (SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U (ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.affine R X) p t)
    (leOfHom (Pi.π (U ∘ t) 0)) n r hr

theorem bidegree (n p : ℕ) (r : R) (hr : r ∈ nonZeroDivisors R) :
    IsSMulRegular (((ProperDeRhamCechFiniteness.BaseSmoothProperDeRhamCechFiniteness.bicomplex R X).X n).X p) r := by
  change IsSMulRegular (∏ᶜ (fun t : Fin (p + 1) → I =>
    ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n).obj.obj (op (∏ᶜ (U ∘ t)))) : ModuleCat.{u} R) r
  exact NumberTheory.PadicHodge.GeometricComparison.Module.TotalRegularity.ModuleTotalRegularity.product _ r (fun t => intersection R X n p t r hr)

theorem total (n : ℕ) (r : R) (hr : r ∈ nonZeroDivisors R) :
    IsSMulRegular ((ProperDeRhamCechFiniteness.BaseSmoothProperDeRhamCechFiniteness.total R X).X n) r :=
  NumberTheory.PadicHodge.GeometricComparison.Module.TotalRegularity.ModuleTotalRegularity.total (ProperDeRhamCechFiniteness.BaseSmoothProperDeRhamCechFiniteness.bicomplex R X) r
    (fun q p => bidegree R X q p r hr) n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperCechRegularity.BaseSmoothProperCechRegularity
