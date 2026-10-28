import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.TraceTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PureFactorizationTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PureTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.DualMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.FixedMap

/-! # Trace Adjunction Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TraceAdjunctionNaturality

noncomputable section

/-! Native projective Serre naturality transported through actual
coefficient adjunctions, before specializing the coefficient sheaves. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality
variable (M N : (Proj (homogeneousSubmodule σ R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent] [N.IsFiniteType]
  (B n : ℕ) (hn : Fintype.card σ = n + 2) (hB : n + 2 ≤ B)
  (c : ℕ)
  (hM : ∀ q, q ≠ c → (ProjectiveRefinement.Serre.fixedDual M B n hn).ExactAt q)
  (hN : ∀ q, q ≠ c → (ProjectiveRefinement.Serre.fixedDual N B n hn).ExactAt q)
  (f : M ⟶ N)
  (i : ℕ) (hi : i + c = n + 1)
  (vM : PureTrace.cohomology M 0) (vN : PureTrace.cohomology N 0)
  (hv : (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) 0).map f vM = vN)

include hv in
theorem refinement_naturality :
    (ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := σ) i).map
        (ProjectiveRefinement.FixedMap.map M N B n hn hB f c) ≫
      PureTrace.trace M B n hn hB c hM i hi vM =
    PureTrace.trace N B n hn hB c hN i hi vN :=
  PureFactorizationTrace.naturality M B n hn hB c hM N hN f
    (ProjectiveRefinement.FixedMap.map M N B n hn hB f c)
    (ProjectiveRefinement.FixedMap.map_left M N B n hn hB f c)
    i hi vM vN hv

variable
  (VM VN : (Proj (homogeneousSubmodule σ R)).Modules)
  (a : (ProjectiveRefinement.Serre.fixedDual M B n hn).homology c ≅ VM)
  (b : (ProjectiveRefinement.Serre.fixedDual N B n hn).homology c ≅ VN)
  (t : VN ⟶ VM)
  (ht : b.hom ≫ t = ProjectiveRefinement.DualMap.map M N
    (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B (n + 2) hB f c ≫ a.hom)

abbrev naturality := Functor.TraceTransport.transportInferred
  (refinement_naturality M N B n hn hB c hM hN f i hi vM vN hv) a b t ht

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TraceAdjunctionNaturality
