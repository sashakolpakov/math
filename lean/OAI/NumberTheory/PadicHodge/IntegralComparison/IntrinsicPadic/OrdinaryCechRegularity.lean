import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.OrdinaryCechUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalRegularity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CohomologyDetection
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralReductionCoordinates

/-! # Ordinary Cech Regularity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.OrdinaryCechRegularity.IntrinsicOrdinary

noncomputable section

/-! Every degree of the genuine ordinary coordinate Čech total is
p-regular; its coefficient-power reductions detect all cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p])))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]

local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "B" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.OrdinaryCechUnit.IntrinsicOrdinary.bicomplex p X

theorem forms (q : ℕ) (t : Fin (q+1) → GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X) (n : ℕ) :
    IsSMulRegular ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf ℤ_[p] X n).obj (op (∏ᶜ (U ∘ t))))
      (p : ℤ_[p]) := by
  have hI : IsAffineOpen (∏ᶜ (U ∘ t)) := by
    rw [AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation.AffineOpenFiniteProductPreservation.product_iInf]
    exact IsAffineOpen.iInf (fun j => GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.affine ℤ_[p] X (t j))
  let I : X.left.affineOpens := ⟨∏ᶜ (U ∘ t), hI⟩
  have hi : I.val ≤ U (t 0) := leOfHom (Pi.π (U ∘ t) 0)
  let σ := GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.coordinateIndex ℤ_[p] X (t 0)
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  let : Algebra (MvPolynomial σ ℤ_[p]) (AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenFormRegularity.BaseAffineOpenFormRegularity.ring ℤ_[p] X I.val) :=
    GeometricComparison.IntrinsicPadic.EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.padicPolynomialAlgebra p X I (t 0) hi
  let : IsScalarTower ℤ_[p] (MvPolynomial σ ℤ_[p])
      (AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenFormRegularity.BaseAffineOpenFormRegularity.ring ℤ_[p] X I.val) :=
    GeometricComparison.IntrinsicPadic.EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.padicTower p X I (t 0) hi
  let : Algebra.Etale (MvPolynomial σ ℤ_[p])
      (AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenFormRegularity.BaseAffineOpenFormRegularity.ring ℤ_[p] X I.val) :=
    GeometricComparison.IntrinsicPadic.EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.padicEtale p X I (t 0) hi
  exact AlgebraicGeometry.Crystalline.Cohomology.Base.EtaleOrdinaryFormRegularity.BaseEtaleOrdinaryFormRegularity.forms ℤ_[p]
    (AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenFormRegularity.BaseAffineOpenFormRegularity.ring ℤ_[p] X I.val) σ n (p : ℤ_[p])
    (mem_nonZeroDivisors_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))

theorem component_regular (n q : ℕ) : IsSMulRegular (((B).X n).X q) (p : ℤ_[p]) := by
  change IsSMulRegular (∏ᶜ (fun t : Fin (q+1) → GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X =>
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf ℤ_[p] X n).obj (op (∏ᶜ (U ∘ t)))) : ModuleCat ℤ_[p]) (p : ℤ_[p])
  exact GeometricComparison.Module.TotalRegularity.ModuleTotalRegularity.product _ _ (fun t => forms p X q t n)

theorem total_regular (n : ℕ) : IsSMulRegular (((B).total (.up ℕ)).X n) (p : ℤ_[p]) :=
  GeometricComparison.Module.TotalRegularity.ModuleTotalRegularity.total B (p : ℤ_[p]) (component_regular p X) n

theorem eq_zero (i : ℕ) (x : ((B).total (.up ℕ)).homology i)
    (hx : ∀ n, GeometricComparison.CochainQuotientCohomology.PrincipalCochainQuotient.reduction ℤ_[p] ((B).total (.up ℕ))
      (p : ℤ_[p]) (n+1) i x = 0) : x = 0 := by
  let : IsAdicComplete (Ideal.span {(p : ℤ_[p])}) ℤ_[p] := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  let : Module.Finite ℤ_[p] (((B).total (.up ℕ)).homology i) :=
    OrdinaryCechUnit.IntrinsicOrdinary.finite p X i
  exact Principal.CohomologyDetection.finite_eq_zero ℤ_[p] ((B).total (.up ℕ))
    (p : ℤ_[p]) (total_regular p X) i x hx

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.OrdinaryCechRegularity.IntrinsicOrdinary
