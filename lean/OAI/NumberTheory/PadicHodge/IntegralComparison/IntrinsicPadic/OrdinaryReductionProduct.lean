import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.OrdinaryReduction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.IdealQuotientProduct

/-! # Ordinary Reduction Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.OrdinaryReductionProduct.IntrinsicOrdinary

noncomputable section

/-! The full native ordinary coefficient reduction preserves its
integral wedge/Alexander–Whitney product on actual cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p])))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] (n : ℕ)

local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex ℤ_[p] X
local notation "I" => (Ideal.span {(p : ℤ_[p])}) ^ (n+1)
local notation "μ" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.CechProduct.sectionPairing ℤ_[p] X
local notation "hμ" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.CechProduct.sectionPairing_natural ℤ_[p] X
local notation "dμ" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.CechProduct.sectionPairing_differential ℤ_[p] X

abbrev cup := Presheaf.IdealQuotientProduct.cohomologyCup I P μ hμ dμ N

omit [X.left.IsSeparated] in
theorem reduction_cup (i j : ℕ)
    (x : (IntegralDeRham.CechProduct.total ℤ_[p] X N).homology i)
    (y : (IntegralDeRham.CechProduct.total ℤ_[p] X N).homology j) :
    OrdinaryReduction.IntrinsicOrdinary.reduction p X n (i+j)
        (IntegralDeRham.CechProduct.cohomologyCup ℤ_[p] X N i j x y) =
      cup p X n i j (OrdinaryReduction.IntrinsicOrdinary.reduction p X n i x)
        (OrdinaryReduction.IntrinsicOrdinary.reduction p X n j y) :=
  Presheaf.IdealQuotientProduct.map_cohomologyCup I P μ hμ dμ N i j x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.OrdinaryReductionProduct.IntrinsicOrdinary
