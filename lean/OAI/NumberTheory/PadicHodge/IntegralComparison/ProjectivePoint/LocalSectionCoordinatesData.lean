import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalSectionClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ReferenceUnitClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.CoefficientLocalClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.PureCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarForgetEvaluation

/-! # Local Section Coordinates Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalSectionCoordinatesData

noncomputable section

/-! The original local point and survivor maps in their precise
principal and ordinary global cohomology coordinates. -/
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

private abbrev base := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2))
private abbrev cover := AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n+2))
private abbrev cover_affine := AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R) (σ := Fin (n+2))
private abbrev cover_full := AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := Fin (n+2))
abbrev family := PrincipalPoint.Fraction.family U t

abbrev pointSource (q : ℕ) :=
  (Supported.CechHomotopyEquivalence.functor (family U t) q).obj
    (LocalCoordinates.principalDual i s₀ B U hU)
abbrev output := (ProjectiveRefinement.Serre.cohomologyFunctor (R := R)
  (σ := Fin (n+2)) g).obj ((Scheme.Modules.pushforward i).obj N)

def transfer (q : ℕ) := by
  letI : ∀ r, ((GlobalTransferRecovery.coefficientDual B M).X r).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.fixed_dual_qc M (Survivor.chart (R := R)) B (n+2) hB
  letI : ∀ r, ((GlobalTransferRecovery.commonDual i s₀ B M v).X r).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.common_dual_qc M (Survivor.coefficient i s₀)
      (Survivor.chart (R := R)) B (n+2) hB v
  letI := ProjectiveRefinement.DualMap.left_quasiIso M (Survivor.coefficient i s₀)
    (Survivor.chart (R := R)) B (n+2) hB v
  exact Principal.RelativeTransfer.map U hU (family U t) q
    (GlobalTransferRecovery.left i s₀ B M v) (GlobalTransferRecovery.right i s₀ B M v)

def evaluationMap (q : ℕ) (hq : q=n+1) :
    (Principal.AdditiveSections.forgetScalars U).obj
      ((PrincipalReference.Concentration.Reference.functor U hU (family U t) q).obj (GlobalTransferRecovery.coefficientDual B M)) ⟶
        output (g := g) i N := by
  subst q
  exact LocalSectionData.Class.localOutput
    (i := i) (s₀ := s₀) (B := B) (hB := hB) (M := M) (d := c) (hM := hM)
    (N := N) (e := e) (U := U) (hU := hU) (hcontains := hcontains) (a := s) (t := t)
    (ha := hs) (hat := hst) (g := g) (hg := (Nat.add_comm g c).trans hcg)

omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
private theorem evaluationMap_original (q : ℕ) (hq : q=n+1) :
    evaluationMap i s₀ B hB M hM N e U hU hcontains s t hs hst hcg q hq =
      letI : ∀ r, ((GlobalTransferRecovery.coefficientDual B M).X r).IsQuasicoherent :=
        ProjectiveRefinement.AffineTerms.fixed_dual_qc M (Survivor.chart (R := R)) B (n+2) hB
      (Principal.AdditiveSections.forgetScalars U).map
        (PrincipalPoint.PureCoordinates.localPure i U hU t (GlobalTransferRecovery.coefficientDual B M) c hM N e q) ≫
      PrincipalPoint.SingleCoordinates.originalMap (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2)))
        i s₀ U hU hcontains s t hs ((KoszulPoint.Ideal.append _ s t).symm.trans hst)
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n+2)))
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := Fin (n+2)))
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R) (σ := Fin (n+2)))
        N c q (hq.trans ((Nat.add_comm g c).trans hcg).symm) := by
  subst q
  let : ∀ r, ((GlobalTransferRecovery.coefficientDual B M).X r).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.fixed_dual_qc M (Survivor.chart (R := R)) B (n+2) hB
  simp only [evaluationMap, LocalSectionData.Class.localOutput,
    PrincipalPoint.PureCoordinates.localPure, PrincipalPoint.SingleCoordinates.originalMap,
    PrincipalPoint.SingleCoordinates.family, PrincipalPoint.SingleCoordinates.coefficient]

abbrev evaluationAt (q : ℕ) (hq : q=n+1) : pointSource i s₀ B U hU t q → output (g := g) i N :=
  fun x => evaluationMap i s₀ B hB M hM N e U hU hcontains s t hs hst hcg q hq
    (transfer i s₀ B hB M v U hU t q x)

def survivorMap (q : ℕ) :
    (PrincipalReference.Concentration.Reference.functor U hU (family U t) q).obj (GlobalTransferRecovery.coefficientDual B M) ⟶
      (Supported.CechHomotopyEquivalence.functor (family U t) q).obj
        ((single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤
          ModuleCat Γ(Proj (homogeneousSubmodule (Fin (n+2)) R),U)) (.up ℕ) c).obj
            ((Principal.ModuleFunctor.functor U hU).obj ((Scheme.Modules.pushforward i).obj N))) := by
  letI : ∀ r, ((GlobalTransferRecovery.coefficientDual B M).X r).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.fixed_dual_qc M (Survivor.chart (R := R)) B (n+2) hB
  exact PrincipalPoint.PureCoordinates.localMap i U hU t (GlobalTransferRecovery.coefficientDual B M) c hM N e q

variable (eM : Projective.TopTracePairing.coefficientRing R ≃ₗ[
    Projective.TopTracePairing.coefficientRing R] ProjectiveTower.UnitTrace.cohomology M 0)

def globalClass : output (g := g) i N :=
  (ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := Fin (n+2)) g).map e.hom
    (Projective.UnitPureClass.pureClass M (Survivor.coefficient i s₀) B n (Fintype.card_fin (n+2)) hB
      v eM (Projective.SectionClass.pointUnitIso i s₀ hbase) c hM g ((Nat.add_comm g c).trans hcg))

def localClass :=
  survivorMap i B hB M hM N e U hU t (c+g)
    (CoefficientLocalClass.value i s₀ hbase B hB M v U hU s t hst hcg)

def ordinaryMap :
    (Principal.AdditiveSections.forgetScalars U).obj
      ((Supported.CechHomotopyEquivalence.functor (family U t) (c+g)).obj
        ((single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤
          ModuleCat Γ(Proj (homogeneousSubmodule (Fin (n+2)) R),U)) (.up ℕ) c).obj
            ((Principal.ModuleFunctor.functor U hU).obj ((Scheme.Modules.pushforward i).obj N)))) ⟶
      output (g := g) i N :=
  (Principal.AdditiveSections.forgetScalars U).map
    (Principal.SingleModuleCoordinates.moduleCoordinates U hU ((Scheme.Modules.pushforward i).obj N)
      c (family U t) g (c+g) (Nat.add_comm c g)).hom ≫
  PrincipalPoint.SingleCoordinates.coefficientComparison (base (R := R) (n := n))
    i s₀ U hU hcontains s t hs ((KoszulPoint.Ideal.append _ s t).symm.trans hst)
    (cover (R := R) (n := n)) (cover_full (R := R) (n := n)) (cover_affine (R := R) (n := n))
    N c (c+g) (Nat.add_comm c g)

omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
theorem survivor_coordinates :
    (Principal.AdditiveSections.forgetScalars U).map
      (survivorMap i B hB M hM N e U hU t (c+g)) ≫
      ordinaryMap i s₀ N U hU hcontains s t hs hst =
    evaluationMap i s₀ B hB M hM N e U hU hcontains s t hs hst hcg (c+g) hcg := by
  rw [evaluationMap_original]
  let : ∀ r, ((GlobalTransferRecovery.coefficientDual B M).X r).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.fixed_dual_qc M (Survivor.chart (R := R)) B (n+2) hB
  exact PrincipalPoint.PureCoordinates.coordinates (base (R := R) (n := n)) i s₀ U hU hcontains
    s t hs ((KoszulPoint.Ideal.append _ s t).symm.trans hst)
    (cover (R := R) (n := n)) (cover_full (R := R) (n := n)) (cover_affine (R := R) (n := n))
    (GlobalTransferRecovery.coefficientDual B M) c hM N e (c+g) (Nat.add_comm c g)

omit [IsArtinianRing R] [IsLocalRing R] [X.IsSeparated] [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
theorem transfer_value :
    transfer i s₀ B hB M v U hU t (c+g)
      (LocalCoordinates.pointAt i s₀ hbase B hB U hU s t hst hcg) =
    CoefficientLocalClass.value i s₀ hbase B hB M v U hU s t hst hcg := by
  rfl

omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
theorem survivor_coordinates_apply
    (x : (PrincipalReference.Concentration.Reference.functor U hU (family U t) (c+g)).obj
      (GlobalTransferRecovery.coefficientDual B M)) :
    ordinaryMap i s₀ N U hU hcontains s t hs hst
      (survivorMap i B hB M hM N e U hU t (c+g) x) =
    evaluationMap i s₀ B hB M hM N e U hU hcontains s t hs hst hcg (c+g) hcg x :=
  ScalarForgetEvaluation.composite
    (survivorMap i B hB M hM N e U hU t (c+g))
    (ordinaryMap i s₀ N U hU hcontains s t hs hst)
    (evaluationMap i s₀ B hB M hM N e U hU hcontains s t hs hst hcg (c+g) hcg)
    (survivor_coordinates i s₀ B hB M hM N e U hU hcontains s t hs hst hcg) x

omit [IsArtinianRing R] [IsLocalRing R] [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
theorem ordinary_coordinates :
    ordinaryMap i s₀ N U hU hcontains s t hs hst
      (localClass i s₀ hbase B hB M v hM N e U hU s t hst hcg) =
    evaluationAt i s₀ B hB M v hM N e U hU hcontains s t hs hst hcg (c+g) hcg
      (LocalCoordinates.pointAt i s₀ hbase B hB U hU s t hst hcg) := by
  have h := survivor_coordinates_apply i s₀ B hB M hM N e U hU hcontains s t hs hst hcg
    (CoefficientLocalClass.value i s₀ hbase B hB M v U hU s t hst hcg)
  dsimp only [evaluationAt]
  rw [transfer_value i s₀ hbase B hB M v U hU s t hst hcg]
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalSectionCoordinatesData
