import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ReferenceTransfer
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TotalUnitIntrinsicClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.UnitPureClass

/-! # Reference Unit Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ReferenceUnitClass.Reference

noncomputable section

/-! The actual principal transfer, original cover comparison and native
coordinates recover the original total unit class. Concentration and a
specified survivor adjunction therefore recover that same section class. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing
  GlobalTransferRecovery
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
  Survivor.coefficient_qc Survivor.coefficient_finite
variable {X : Scheme.{u}} [X.IsSeparated]
  (i : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R)) [IsClosedImmersion i]
  [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  (s₀ : Spec (CommRingCat.of R) ⟶ X) [IsClosedImmersion s₀]
  (hbase : s₀ ≫ (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _) (B : ℕ) (hB : n+2 ≤ B)
  (M : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] (v : M ⟶ Survivor.coefficient i s₀)
  (d : ℕ) (hM : ∀ q, q ≠ d → (GlobalTransferRecovery.coefficientDual B M).ExactAt q)
  (N : X.Modules) [N.IsQuasicoherent]
  (e : (GlobalTransferRecovery.coefficientDual B M).homology d ≅ (Scheme.Modules.pushforward i).obj N)
  (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens) (hU : IsAffineOpen U)
  (hcontains : ⊤ ≤ (s₀ ≫ i) ⁻¹ᵁ U)
  {c g : ℕ} (a : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (t : Fin g → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (ha : Ideal.span (Set.range a) = i.ker.ideal ⟨U, hU⟩)
  (hat : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) a t =
    (s₀ ≫ i).ker.ideal ⟨U, hU⟩)
  (eM : Projective.TopTracePairing.coefficientRing R ≃ₗ[Projective.TopTracePairing.coefficientRing R] ProjectiveTower.UnitTrace.cohomology M 0)

abbrev unit_recovery := by
  have h := ReferenceTransfer.Reference.point_recovery i s₀ hbase B hB M v
    d hM N e U hU hcontains a t ha hat
  change _ = Projective.TotalUnitMap.unitClass M (Survivor.coefficient i s₀) B n
    (Fintype.card_fin (n+2)) hB v eM
    (Projective.SectionClass.pointUnitIso i s₀ hbase) at h
  exact h

variable (k : ℕ) (hk : k+d=n+1)

abbrev pure_recovery := by
  have h := unit_recovery i s₀ hbase B hB M v d hM N e U hU hcontains a t ha hat eM
  exact congrArg
    (Projective.UnitPureClass.concentration M B n (Fintype.card_fin (n+2)) hB
      d hM k hk).hom h

abbrev section_recovery := by
  have h := pure_recovery i s₀ hbase B hB M v d hM N e U hU hcontains a t ha hat eM k hk
  exact congrArg
    ((ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := Fin (n+2)) k).map e.hom) h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ReferenceUnitClass.Reference
