import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.UnitPureClass

/-! # Pure Class Degree Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PureClassDegreeTransport

noncomputable section

/-! Changing the name of the unique surviving degree preserves the
original projective pure class and the transported survivor map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.UnitTrace
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (M P N : (Proj (homogeneousSubmodule σ R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] [P.IsQuasicoherent] [P.IsFiniteType]
  (B n : ℕ) (hn : Fintype.card σ=n+2) (hB : n+2≤B) (f : M ⟶ P)
  (eM : TopTracePairing.coefficientRing R ≃ₗ[TopTracePairing.coefficientRing R] ProjectiveTower.UnitTrace.cohomology M 0)
  (eP : TopTracePairing.coefficientRing R ≃ₗ[TopTracePairing.coefficientRing R] ProjectiveTower.UnitTrace.cohomology P 0)
  (c d : ℕ) (hcd : c=d)
  (hC : ∀ q, q≠c → (ProjectiveRefinement.Serre.fixedDual M B n hn).ExactAt q)
  (hD : ∀ q, q≠d → (ProjectiveRefinement.Serre.fixedDual M B n hn).ExactAt q)
  (g : ℕ) (hgC : g+c=n+1) (hgD : g+d=n+1)
  (e : (ProjectiveRefinement.Serre.fixedDual M B n hn).homology d ≅ N)

theorem comparison :
    (ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := σ) g).map
      (eqToIso (congrArg (fun j => (ProjectiveRefinement.Serre.fixedDual M B n hn).homology j) hcd) ≪≫ e).hom
      (UnitPureClass.pureClass M P B n hn hB f eM eP c hC g hgC) =
    (ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := σ) g).map e.hom
      (UnitPureClass.pureClass M P B n hn hB f eM eP d hD g hgD) := by
  subst d
  simp only [eqToIso_refl, Iso.refl_trans]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PureClassDegreeTransport
