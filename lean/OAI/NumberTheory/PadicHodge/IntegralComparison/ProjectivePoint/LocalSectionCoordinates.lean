import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.BaseRecovery

/-! # Local Section Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalSectionCoordinates

noncomputable section

/-! The original fixed point at the full Koszul degree recovers the
same original global section through its actual principal coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

private theorem constrained_apply {F : ℕ → Type u} {G : Type u} {n q : ℕ}
    (a : ∀ j, j=n → F j → G) (h : q=n) (x : F n) :
    a q h (Eq.mpr (congrArg F h) x) = a n rfl x := by
  subst q
  rfl

open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.GlobalTransferRecovery
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n c g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
  Survivor.coefficient_qc Survivor.coefficient_finite
variable {X : Scheme.{u}} [X.IsSeparated]
  (i : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R)) [IsClosedImmersion i]
  [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  (s₀ : Spec (CommRingCat.of R) ⟶ X) [IsClosedImmersion s₀]
  (hbase : s₀ ≫ (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _) (B : ℕ) (hB : n+2≤B)
  (M : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] (v : M ⟶ Survivor.coefficient i s₀)
  (hM : ∀ q, q ≠ c → (GlobalTransferRecovery.coefficientDual B M).ExactAt q)
  (N : X.Modules) [N.IsQuasicoherent]
  (e : (GlobalTransferRecovery.coefficientDual B M).homology c ≅ (Scheme.Modules.pushforward i).obj N)
  (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens) (hU : IsAffineOpen U)
  (hcontains : ⊤ ≤ (s₀ ≫ i) ⁻¹ᵁ U)
  (s : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R),U))
  (t : Fin g → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R),U))
  (hs : Ideal.span (Set.range s) = i.ker.ideal ⟨U,hU⟩)
  (hst : KoszulPartial.Resolution.pointIdeal
    Γ(Proj (homogeneousSubmodule (Fin (n+2)) R),U) s t = (s₀ ≫ i).ker.ideal ⟨U,hU⟩)
  (hcg : c+g=n+1)

variable (eM : Projective.TopTracePairing.coefficientRing R ≃ₗ[
    Projective.TopTracePairing.coefficientRing R] ProjectiveTower.UnitTrace.cohomology M 0)

omit [IsArtinianRing R] [IsLocalRing R] [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
private theorem point_degree_evaluation :
    LocalSectionCoordinatesData.evaluationAt i s₀ B hB M v hM N e U hU hcontains s t hs hst hcg (c+g) hcg
      (LocalCoordinates.pointAt i s₀ hbase B hB U hU s t hst hcg) =
    LocalSectionCoordinatesData.evaluationAt i s₀ B hB M v hM N e U hU hcontains s t hs hst hcg (n+1) rfl
      (LocalClass.pointClass i s₀ hbase B hB U hU s t hst) :=
  (constrained_apply
    (F := fun q => (Supported.CechHomotopyEquivalence.functor (LocalSectionCoordinatesData.family U t) q).obj
      (LocalCoordinates.principalDual i s₀ B U hU))
    (G := LocalSectionCoordinatesData.output (g := g) i N)
    (LocalSectionCoordinatesData.evaluationAt i s₀ B hB M v hM N e U hU hcontains s t hs hst hcg) hcg
    (LocalClass.pointClass i s₀ hbase B hB U hU s t hst))

omit [IsArtinianRing R] [IsLocalRing R] [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
theorem recovery :
    LocalSectionCoordinatesData.evaluationAt i s₀ B hB M v hM N e U hU hcontains s t hs hst hcg (c+g) hcg
      (LocalCoordinates.pointAt i s₀ hbase B hB U hU s t hst hcg) =
    LocalSectionCoordinatesData.globalClass i s₀ hbase B hB M v hM N e hcg eM :=
  (point_degree_evaluation i s₀ hbase B hB M v hM N e U hU hcontains s t hs hst hcg).trans
    (BaseRecovery.LocalSectionCoordinates.base_recovery i s₀ hbase B hB M v hM N e U hU hcontains s t hs hst hcg eM)

omit [IsArtinianRing R] [IsLocalRing R] [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
theorem ordinary_recovery :
    LocalSectionCoordinatesData.ordinaryMap i s₀ N U hU hcontains s t hs hst
      (LocalSectionCoordinatesData.localClass i s₀ hbase B hB M v hM N e U hU s t hst hcg) =
    LocalSectionCoordinatesData.globalClass i s₀ hbase B hB M v hM N e hcg eM :=
  (LocalSectionCoordinatesData.ordinary_coordinates i s₀ hbase B hB M v hM N e U hU hcontains s t hs hst hcg).trans
    (recovery i s₀ hbase B hB M v hM N e U hU hcontains s t hs hst hcg eM)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalSectionCoordinates
