import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.OrdinaryCechRegularity
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.QuotientProjection
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.CechQuotientTotal

/-! # Ordinary Reduction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.OrdinaryReduction.IntrinsicOrdinary

noncomputable section

/-! Coefficient reduction of the full ordinary coordinate Čech complex
is the literal pointwise reduction on forms. These maps detect its
original cohomology classes in all degrees. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p])))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]

local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "E" => FormalCoproduct.cech (FormalCoproduct.mk (OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X) U)
local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex ℤ_[p] X
local notation "C" => HomologicalComplex₂.total (OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.OrdinaryCechUnit.IntrinsicOrdinary.bicomplex p X) (ComplexShape.up ℕ)
local notation "Ip" => (Ideal.span {(p : ℤ_[p])})

def iso (n : ℕ) : GeometricComparison.PrincipalCochainExact.PrincipalCochainQuotient.quotient ℤ_[p] C (p : ℤ_[p]) (n+1) ≅
    (GeometricComparison.IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.bicomplex ℤ_[p] X U (Ip ^ (n+1))).total (.up ℕ) :=
  GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.totalIso (Module.IdealQuotient.functor ℤ_[p] (Ip ^ (n+1)))
    E (GeometricComparison.IntegralCech.QuotientTotal.IntegralCechQuotientTotal.finiteIndices ℤ_[p] X U) P

def map (n : ℕ) := GeometricComparison.CechPresheaf.QuotientProjection.CechPresheafQuotientProjection.map ℤ_[p] (Ip ^ (n+1)) E P

omit [X.left.IsSeparated] in
theorem coordinates (n : ℕ) :
    GeometricComparison.PrincipalCochainExact.PrincipalCochainQuotient.projection ℤ_[p] C (p : ℤ_[p]) (n+1) ≫ (iso p X n).hom = map p X n :=
  GeometricComparison.CechPresheaf.QuotientProjection.CechPresheafQuotientProjection.total ℤ_[p] (Ip ^ (n+1)) E
    (GeometricComparison.IntegralCech.QuotientTotal.IntegralCechQuotientTotal.finiteIndices ℤ_[p] X U) P

def reduction (n i : ℕ) := (HomologicalComplex.homologyMap (map p X n) i).hom

omit [X.left.IsSeparated] in
theorem reduction_coordinates (n i : ℕ) (x : (C).homology i) :
    reduction p X n i x = HomologicalComplex.homologyMap (iso p X n).hom i
      (GeometricComparison.CochainQuotientCohomology.PrincipalCochainQuotient.reduction ℤ_[p] C (p : ℤ_[p]) (n+1) i x) := by
  have h := congrArg (fun f => HomologicalComplex.homologyMap f i) (coordinates p X n)
  rw [HomologicalComplex.homologyMap_comp] at h
  exact (ConcreteCategory.congr_hom h x).symm

theorem eq_zero (i : ℕ) (x : (C).homology i) (hx : ∀ n, reduction p X n i x = 0) : x = 0 := by
  apply OrdinaryCechRegularity.IntrinsicOrdinary.eq_zero p X i x
  intro n
  apply (HomologicalComplex.homologyMapIso (iso p X n) i).toLinearEquiv.injective
  rw [map_zero]
  exact (reduction_coordinates p X n i x).symm.trans (hx n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.OrdinaryReduction.IntrinsicOrdinary
