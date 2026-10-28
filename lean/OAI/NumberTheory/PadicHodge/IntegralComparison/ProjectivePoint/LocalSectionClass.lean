import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointLocal

/-! # Local Section Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalSectionClass

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
private theorem precomposeOutput {C : Type*} [Category C] {A B D E : C}
    (f : A ⟶ B) (o : B ⟶ D) (g : B ⟶ E) (p : E ⟶ D) (n : A ⟶ E)
    (ho : o = g ≫ p) (hg : f ≫ g = n) : f ≫ o = n ≫ p := by
  rw [ho, ← Category.assoc, hg]

private theorem recoverFromMaps {A B D E : AddCommGrpCat.{u}}
    (f : A ⟶ B) (o : B ⟶ D) (n : A ⟶ E) (p : E ⟶ D)
    (x : A) (y : E) (h : f ≫ o = n ≫ p) (hu : n x = y) : o (f x) = p y := by
  have hx := ConcreteCategory.congr_hom h x
  simpa only [ConcreteCategory.comp_apply, hu] using hx

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

omit [X.IsSeparated] [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] in
private theorem nativeTransfer_eq :
    LocalSectionData.Class.nativeTransfer i s₀ B hB M v = LocalSectionData.Class.native i s₀ B hB M v := rfl

omit [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] in
private theorem incoming_globalize :
    LocalSectionData.Class.incoming i s₀ hbase B hB M v U hU a t hat ≫
      LocalSectionData.Class.globalize i s₀ B hB M d hM N e U hU hcontains a t ha hat =
        LocalSectionData.Class.native i s₀ B hB M v := by
  have h : LocalSectionData.Class.incoming i s₀ hbase B hB M v U hU a t hat ≫
      LocalSectionData.Class.globalize i s₀ B hB M d hM N e U hU hcontains a t ha hat =
        LocalSectionData.Class.nativeTransfer i s₀ B hB M v := by
    simpa only [LocalSectionData.Class.incoming, LocalSectionData.Class.globalize, LocalSectionData.Class.nativeTransfer, LocalClass.map,
      LocalClass.localize, Category.assoc] using
      ReferenceTransfer.Reference.recovery i s₀ hbase B hB M v
        d hM N e U hU hcontains a t ha hat
  exact h.trans (nativeTransfer_eq i s₀ B hB M v)

omit [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] in
include i s₀ hbase B hB M v d hM N e U hU hcontains a t ha hat g hg in
private abbrev map_comparison :=
  precomposeOutput
    (LocalSectionData.Class.incoming i s₀ hbase B hB M v U hU a t hat) _ _ _ _
    (PointLocal.SectionClass.localOutput_eq (i := i) (s₀ := s₀) (B := B) (hB := hB)
      (M := M) (d := d) (hM := hM) (N := N) (e := e) (U := U) (hU := hU)
      (hcontains := hcontains) (a := a) (t := t) (ha := ha) (hat := hat) (g := g) (hg := hg))
    (incoming_globalize i s₀ hbase B hB M v d hM N e U hU hcontains a t ha hat)

omit [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
omit [IsArtinianRing R] [IsLocalRing R] in
include i s₀ hbase B hB M v d hM N e U hU hcontains a t ha hat g hg in
private abbrev point_comparison :=
  ConcreteCategory.congr_hom
    (map_comparison i s₀ hbase B hB M v d hM N e U hU hcontains a t ha hat g hg)
    (SupportedClass.fixedPointClass i s₀ hbase B hB)

omit [IsArtinianRing R] [IsLocalRing R] [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
theorem recovery :
    LocalSectionData.Class.localOutput i s₀ B hB M d hM N e U hU hcontains a t ha hat g hg
      (LocalSectionData.Class.incoming i s₀ hbase B hB M v U hU a t hat
        (SupportedClass.fixedPointClass i s₀ hbase B hB)) =
    LocalSectionData.Class.pureMap i B hB M d hM N e g hg
      (Projective.TotalUnitMap.unitClass M (Survivor.coefficient i s₀) B n
        (Fintype.card_fin (n+2)) hB v eM (Projective.SectionClass.pointUnitIso i s₀ hbase)) :=
  recoverFromMaps
    (LocalSectionData.Class.incoming i s₀ hbase B hB M v U hU a t hat) _ _ _ _ _
    (map_comparison i s₀ hbase B hB M v d hM N e U hU hcontains a t ha hat g hg)
    (Projective.TotalUnitIntrinsicClass.Intrinsic.unitClass M (Survivor.coefficient i s₀) B n
      (Fintype.card_fin (n+2)) hB v eM (Projective.SectionClass.pointUnitIso i s₀ hbase))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalSectionClass
