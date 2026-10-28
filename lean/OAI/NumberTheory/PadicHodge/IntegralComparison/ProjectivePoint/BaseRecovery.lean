import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalSectionCoordinatesData
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalSectionClass

/-! # Base Recovery -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.BaseRecovery.LocalSectionCoordinates

noncomputable section

/-! The original fixed point at the full Koszul degree recovers the
same original global section through its actual principal coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

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

omit [X.IsSeparated] [IsArtinianRing R] [IsLocalRing R] [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
private theorem transfer_point_original :
    LocalSectionCoordinatesData.transfer i s₀ B hB M v U hU t (n+1)
      (LocalClass.pointClass i s₀ hbase B hB U hU s t hst) =
    LocalSectionData.Class.incoming i s₀ hbase B hB M v U hU s t hst
      (SupportedClass.fixedPointClass i s₀ hbase B hB) := by
  rfl

omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
private theorem evaluation_original :
    LocalSectionCoordinatesData.evaluationMap i s₀ B hB M hM N e U hU hcontains s t hs hst hcg (n+1) rfl =
    LocalSectionData.Class.localOutput i s₀ B hB M c hM N e
      U hU hcontains s t hs hst g ((Nat.add_comm g c).trans hcg) := by
  rfl

omit [X.IsSeparated] [N.IsQuasicoherent] [IsArtinianRing R] [IsLocalRing R] [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
private theorem global_class_original :
    LocalSectionData.Class.pureMap i B hB M c hM N e g
      ((Nat.add_comm g c).trans hcg)
      (Projective.TotalUnitMap.unitClass M (Survivor.coefficient i s₀) B n
        (Fintype.card_fin (n+2)) hB v eM (Projective.SectionClass.pointUnitIso i s₀ hbase)) =
    LocalSectionCoordinatesData.globalClass i s₀ hbase B hB M v hM N e hcg eM := by
  rfl

omit [IsArtinianRing R] [IsLocalRing R] [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
theorem base_recovery :
    LocalSectionCoordinatesData.evaluationAt i s₀ B hB M v hM N e U hU hcontains s t hs hst hcg (n+1) rfl
      (LocalClass.pointClass i s₀ hbase B hB U hU s t hst) =
    LocalSectionCoordinatesData.globalClass i s₀ hbase B hB M v hM N e hcg eM := by
  dsimp only [LocalSectionCoordinatesData.evaluationAt]
  rw [evaluation_original, transfer_point_original]
  rw [← global_class_original i s₀ hbase B hB M v hM N e hcg eM]
  exact LocalSectionClass.recovery i s₀ hbase B hB M v c hM N e
    U hU hcontains s t hs hst eM g ((Nat.add_comm g c).trans hcg)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.BaseRecovery.LocalSectionCoordinates
