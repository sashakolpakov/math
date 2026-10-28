import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ReducedBaseTotalProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.AssemblyCoefficientCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.RestrictScalarsCochainCup
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient

/-! # Witt Total Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.WittTotalProduct.Intrinsic

noncomputable section

/-! Multiplicativity of the exact Witt-total isomorphism in the
original finite ordinary comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

private theorem inverse_pairing {R : Type*} [CommRing R]
    {K L : CochainComplex (ModuleCat R) ℕ} (e : K ≅ L)
    (μ : ∀ i j, K.X i →ₗ[R] K.X j →ₗ[R] K.X (i+j))
    (ν : ∀ i j, L.X i →ₗ[R] L.X j →ₗ[R] L.X (i+j))
    (h : ∀ i j x y, e.hom.f (i+j) (μ i j x y) = ν i j (e.hom.f i x) (e.hom.f j y))
    (i j : ℕ) (x : L.X i) (y : L.X j) :
    e.inv.f (i+j) (ν i j x y) = μ i j (e.inv.f i x) (e.inv.f j y) := by
  let ei := ((HomologicalComplex.eval _ _ i).mapIso e).toLinearEquiv
  let ej := ((HomologicalComplex.eval _ _ j).mapIso e).toLinearEquiv
  let eij := ((HomologicalComplex.eval _ _ (i+j)).mapIso e).toLinearEquiv
  change eij.symm (ν i j x y) = μ i j (ei.symm x) (ej.symm y)
  apply eij.injective
  exact (eij.apply_symm_apply _).trans
    ((congrArg₂ (fun x y => ν i j x y) (ei.apply_symm_apply x).symm
      (ej.apply_symm_apply y).symm).trans
      (h i j (ei.symm x) (ej.symm y)).symm)

private theorem trans_pairing {R : Type*} [CommRing R]
    {K L M : CochainComplex (ModuleCat R) ℕ} (e : K ≅ L) (f : L ≅ M)
    (μ : ∀ i j, K.X i →ₗ[R] K.X j →ₗ[R] K.X (i+j))
    (ν : ∀ i j, L.X i →ₗ[R] L.X j →ₗ[R] L.X (i+j))
    (σ : ∀ i j, M.X i →ₗ[R] M.X j →ₗ[R] M.X (i+j))
    (he : ∀ i j x y, e.hom.f (i+j) (μ i j x y) = ν i j (e.hom.f i x) (e.hom.f j y))
    (hf : ∀ i j x y, f.hom.f (i+j) (ν i j x y) = σ i j (f.hom.f i x) (f.hom.f j y))
    (i j : ℕ) (x : K.X i) (y : K.X j) :
    (e ≪≫ f).hom.f (i+j) (μ i j x y) =
      σ i j ((e ≪≫ f).hom.f i x) ((e ≪≫ f).hom.f j y) :=
  (congrArg (f.hom.f (i+j)) (he i j x y)).trans (hf i j _ _)

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "IW" => (Ideal.span {(p : W)}) ^ (n+1)
local notation "IZ" => (Ideal.span {(p : ℤ_[p])}) ^ (n+1)
local notation "AW" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X
local notation "AZ" => CategoryTheory.Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left) ⋙
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℤ_[p] X
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct.Ordinary.complex W IW AW
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct.Ordinary.complex ℤ_[p] IZ AZ
local notation "μ" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct.Ordinary.pairing W IW AW
local notation "ν" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct.Ordinary.pairing ℤ_[p] IZ AZ
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local instance coefficients : Algebra W ℤ_[p] := GeometricComparison.WittAlgebra.PadicWittAlgebra.coefficientAlgebra p
local notation "restrict" => ModuleCat.restrictScalars (algebraMap W ℤ_[p])

abbrev sourceCup := Presheaf.TotalCup.CechProduct.totalCup N P μ
abbrev targetCup := RestrictScalarsCochainCup.pairing W ℤ_[p]
  (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.total p X n) (Presheaf.TotalCup.CechProduct.totalCup N Q ν)
abbrev middleCup := Presheaf.TotalCup.CechProduct.totalCup N
  (GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex restrict Q)
  (RestrictScalarsPresheafCup.pairing W ℤ_[p] Q ν)

abbrev coefficientIso := GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso restrict N
  (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.diagram p X n)

theorem coefficient_cup (i j : ℕ)
    (x : (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.total p X n).X i)
    (y : (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.total p X n).X j) :
    ((coefficientIso p X n).hom.f (i+j)) (targetCup p X n i j x y) =
      middleCup p X n i j (((coefficientIso p X n).hom.f i) x)
        (((coefficientIso p X n).hom.f j) y) :=
  Cech.AssemblyCoefficientCup.map_cup restrict (fun M => AddMonoidHom.id M)
    (fun _ _ => rfl) N (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U)
    (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.diagram p X n) ν
    (RestrictScalarsPresheafCup.pairing W ℤ_[p] Q ν) (fun _ _ _ _ _ => rfl) i j x y

abbrev coefficient_inverse_cup := inverse_pairing (coefficientIso p X n)
  (targetCup p X n) (middleCup p X n) (coefficient_cup p X n)

theorem map_cup (i j : ℕ) (x : (GeometricComparison.IntrinsicIntegral.CoefficientTotal.IntrinsicIntegralCoefficientTotal.total p X n).X i)
    (y : (GeometricComparison.IntrinsicIntegral.CoefficientTotal.IntrinsicIntegralCoefficientTotal.total p X n).X j) :
    ((GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X n).hom.f (i+j))
        (sourceCup p X n i j x y) =
      targetCup p X n i j
        (((GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X n).hom.f i) x)
        (((GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X n).hom.f j) y) :=
  trans_pairing (GeometricComparison.CechAssembly.Iso.CechAssemblyIso.totalIso N (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.wittIso p X n))
    (coefficientIso p X n).symm (sourceCup p X n) (middleCup p X n) (targetCup p X n)
    (Presheaf.CechProductNaturality.totalMap_pairing N μ (ReducedBaseTotalProduct.Intrinsic.pairing p X n)
      (ReducedBaseTotalProduct.Intrinsic.map p X n)
      (ReducedBaseTotalProduct.Intrinsic.map_pairing p X n))
    (coefficient_inverse_cup p X n) i j x y

abbrev source_differential := Presheaf.TotalLeibniz.CechProduct.differential_totalCup N P μ
  (OrdinaryQuotientDiagramProduct.Ordinary.natural W IW AW)
  (OrdinaryQuotientDiagramProduct.Ordinary.differential W IW AW)

abbrev target_differential := RestrictScalarsCochainCup.differential W ℤ_[p]
  (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.total p X n) (Presheaf.TotalCup.CechProduct.totalCup N Q ν)
  (Presheaf.TotalLeibniz.CechProduct.differential_totalCup N Q ν (OrdinaryQuotientDiagramProduct.Ordinary.natural ℤ_[p] IZ AZ)
    (OrdinaryQuotientDiagramProduct.Ordinary.differential ℤ_[p] IZ AZ))

abbrev cohomologyMap_cup := Cochain.CupNaturality.Cohomology.cohomologyMap_cup
  (sourceCup p X n) (targetCup p X n) (source_differential p X n) (target_differential p X n)
  (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X n).hom (map_cup p X n)

abbrev inverse_map_cup := inverse_pairing (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X n)
  (sourceCup p X n) (targetCup p X n) (map_cup p X n)

abbrev inverse_cohomologyMap_cup := Cochain.CupNaturality.Cohomology.cohomologyMap_cup
  (targetCup p X n) (sourceCup p X n) (target_differential p X n) (source_differential p X n)
  (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X n).inv (inverse_map_cup p X n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.WittTotalProduct.Intrinsic
