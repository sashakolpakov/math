import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalSectionData

/-! # Concentration Hom -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ConcentrationHom.LocalSectionClass

noncomputable section

/-! The actual local point transfer, after principal concentration and
the genuine survivor adjunction, recovers the original global pure class. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomologicalComplex
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
  {c b : ℕ} (a : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (t : Fin b → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (ha : Ideal.span (Set.range a) = i.ker.ideal ⟨U, hU⟩)
  (hat : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) a t =
    (s₀ ≫ i).ker.ideal ⟨U, hU⟩)
  (eM : Projective.TopTracePairing.coefficientRing R ≃ₗ[Projective.TopTracePairing.coefficientRing R] ProjectiveTower.UnitTrace.cohomology M 0)
  (g : ℕ) (hg : g+d=n+1)
local notation "π" => OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2))
local notation "V" => OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n+2))
local notation "haV" => OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R) (σ := Fin (n+2))
local notation "hV" => OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := Fin (n+2))

omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] in
theorem concentration_hom
    [∀ q : ℕ, ((GlobalTransferRecovery.coefficientDual B M).X q).IsQuasicoherent] :
    (Projective.UnitPureClass.concentration M B n
      (Fintype.card_fin (n+2)) hB d hM g hg).hom =
    (Global.PureIndexedCoordinates.concentration π V haV (GlobalTransferRecovery.coefficientDual B M)
      d hM g (n+1) hg.symm).hom := by
  exact congrArg Iso.hom
    (Projective.UnitConcentrationCoordinates.concentration M B n
      (Fintype.card_fin (n+2)) hB d hM g hg)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ConcentrationHom.LocalSectionClass
