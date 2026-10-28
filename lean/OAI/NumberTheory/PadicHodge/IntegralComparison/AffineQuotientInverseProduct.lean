import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryAffineQuotientProduct

/-! # Affine Quotient Inverse Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineQuotientInverseProduct.Ordinary

noncomputable section

/-! The inverse of the actual affine/open coefficient-quotient Čech
isomorphism preserves the native cohomology products. -/

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

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) [X.left.IsSeparated]
  {ι : Type} (U : ι → X.left.affineOpens) (I : Ideal R)

local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left
local notation "A" => CategoryTheory.Functor.op F ⋙ OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct.Ordinary.complex R I A
local notation "μ" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct.Ordinary.pairing R I A
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.IdealQuotientProduct.complex I (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
local notation "ν" => OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.IdealQuotientProduct.pairing I (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
  (IntegralDeRham.CechProduct.sectionPairing R X)
local notation "hν" => OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.IdealQuotientProduct.natural I (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
  (IntegralDeRham.CechProduct.sectionPairing R X)
  (IntegralDeRham.CechProduct.sectionPairing_natural R X)
local notation "dν" => OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.IdealQuotientProduct.differential I (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
  (IntegralDeRham.CechProduct.sectionPairing R X)
  (IntegralDeRham.CechProduct.sectionPairing_differential R X)
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "N'" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (Functor.obj F ∘ U)

local instance tuple_preserves (n : ℕ) (t : Fin (n+1) → ι) :
    PreservesLimit (Discrete.functor (U ∘ t)) F :=
  GeometricComparison.Affine.OpenProductPreservation.AffineOpenProductPreservation.inclusion_preserves X.left (U ∘ t)

abbrev map_cup := inverse_pairing (GeometricComparison.OrdinaryAffineTotal.OrdinaryAffineQuotientCech.totalIso R X U I)
  (Presheaf.TotalCup.CechProduct.totalCup N P μ) (Presheaf.TotalCup.CechProduct.totalCup N' Q ν)
  (OrdinaryAffineQuotientProduct.OrdinaryTotal.map_cup R X U I)

abbrev cohomologyMap_cup := Cochain.CupNaturality.Cohomology.cohomologyMap_cup
  (Presheaf.TotalCup.CechProduct.totalCup N' Q ν) (Presheaf.TotalCup.CechProduct.totalCup N P μ)
  (Presheaf.TotalLeibniz.CechProduct.differential_totalCup N' Q ν hν dν)
  (Presheaf.TotalLeibniz.CechProduct.differential_totalCup N P μ (OrdinaryQuotientDiagramProduct.Ordinary.natural R I A)
    (OrdinaryQuotientDiagramProduct.Ordinary.differential R I A))
  (GeometricComparison.OrdinaryAffineTotal.OrdinaryAffineQuotientCech.totalIso R X U I).inv (map_cup R X U I)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineQuotientInverseProduct.Ordinary
