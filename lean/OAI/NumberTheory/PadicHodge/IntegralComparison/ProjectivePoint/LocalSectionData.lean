import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.ShiftedMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ReferenceUnitClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.UnitConcentrationCoordinates

/-! # Local Section Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalSectionData.Class

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

theorem replace_middle {D : Type*} [Category D]
    {A B C E F : D} {f : A ⟶ F} {a : A ⟶ B} {b : B ⟶ C}
    {c c' : C ⟶ E} {d : E ⟶ F}
    (h : f = a ≫ b ≫ c ≫ d) (hc : c' = c) : f = a ≫ b ≫ c' ≫ d := by
  rw [hc]
  exact h

include hB in
omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] in
theorem coefficient_quasicoherent : ∀ q : ℕ, ((GlobalTransferRecovery.coefficientDual B M).X q).IsQuasicoherent :=
  ProjectiveRefinement.AffineTerms.fixed_dual_qc M (Survivor.chart (R := R)) B (n+2) hB

abbrev principalGroup : AddCommGrpCat.{u} :=
  (Principal.AdditiveSections.forgetScalars U).obj
    ((PrincipalReference.Concentration.Reference.functor U hU
      (PrincipalPoint.Fraction.family U t) (n+1)).obj (GlobalTransferRecovery.coefficientDual B M))

abbrev nativeGroup
    (L : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Modules)
    [L.IsQuasicoherent] [L.IsFiniteType] : AddCommGrpCat.{u} :=
  (IntrinsicOrdered.CechTransferCoordinates.Intrinsic.nativeFunctor π V (n+1)).obj
    (GlobalTransferRecovery.coefficientDual B L)

abbrev outputGroup : AddCommGrpCat.{u} :=
  (ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := Fin (n+2)) g).obj
    ((Scheme.Modules.pushforward i).obj N)

def globalize : principalGroup B M U hU t ⟶ nativeGroup B M := by
  haveI : ∀ q : ℕ, ((GlobalTransferRecovery.coefficientDual B M).X q).IsQuasicoherent :=
    coefficient_quasicoherent (B := B) (hB := hB) (M := M)
  haveI := CanonicalTransfer.refinement_isIso i s₀ B hB M d hM N e
    U hU a t ha hat
  exact PrincipalReference.CoverTransfer.Reference.comparison U hU
    (PrincipalPoint.Fraction.family U t) (s₀ ≫ i) hcontains
    (PrincipalPoint.RelativeGeometry.common i s₀ U hU t)
    (PrincipalPoint.RelativeGeometry.left i s₀ U hU t)
    (PrincipalPoint.RelativeGeometry.right i s₀ U hU t) V hV haV
    (K := GlobalTransferRecovery.coefficientDual B M) (n+1) ≫
      (IntrinsicOrdered.CechTransferCoordinates.Intrinsic.iso π V (n+1) (GlobalTransferRecovery.coefficientDual B M)).inv

def pureMap : nativeGroup B M ⟶ outputGroup i N g :=
  (Projective.UnitPureClass.concentration M B n
    (Fintype.card_fin (n+2)) hB d hM g hg).hom ≫
  (ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := Fin (n+2)) g).map e.hom

def localOutput : principalGroup B M U hU t ⟶ outputGroup i N g := by
  haveI : ∀ q : ℕ, ((GlobalTransferRecovery.coefficientDual B M).X q).IsQuasicoherent :=
    coefficient_quasicoherent (B := B) (hB := hB) (M := M)
  let D := (Scheme.Modules.pushforward i).obj N
  haveI : D.IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom i
  haveI (k : ℕ) : (((single _ (.up ℕ) d).obj D).X k).IsQuasicoherent :=
    QuasicoherentTruncation.single D d k
  haveI := PrincipalPoint.RelativeGeometry.right_isIso i s₀ U hU a t ha
    ((KoszulPoint.Ideal.append _ a t).symm.trans hat)
    ((single _ (.up ℕ) d).obj D) d
    (fun k hk => exactAt_single_obj (.up ℕ) d D k hk) N
    (singleObjHomologySelfIso (.up ℕ) d D) (n+1)
  exact (Principal.AdditiveSections.forgetScalars U).map
      ((PrincipalReference.Concentration.Reference.iso U hU (PrincipalPoint.Fraction.family U t)
        (GlobalTransferRecovery.coefficientDual B M) d hM (n+1)).hom ≫
      (PrincipalReference.Concentration.Reference.functor U hU
        (PrincipalPoint.Fraction.family U t) (n+1)).map
          ((single _ (.up ℕ) d).map e.hom)) ≫
    PrincipalReference.CoverTransfer.Reference.comparison U hU
      (PrincipalPoint.Fraction.family U t) (s₀ ≫ i) hcontains
      (PrincipalPoint.RelativeGeometry.common i s₀ U hU t)
      (PrincipalPoint.RelativeGeometry.left i s₀ U hU t)
      (PrincipalPoint.RelativeGeometry.right i s₀ U hU t) V hV haV
      (K := (single _ (.up ℕ) d).obj D) (n+1) ≫
    (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π V
      ((single _ (.up ℕ) d).obj D) (n+1)).inv ≫
    (Global.PureIndexedCoordinates.singleIso π V D d g (n+1) hg.symm).hom
def incoming : nativeGroup B (Survivor.coefficient i s₀) ⟶ principalGroup B M U hU t := by
  haveI : ∀ q : ℕ, ((GlobalTransferRecovery.coefficientDual B M).X q).IsQuasicoherent :=
    coefficient_quasicoherent (B := B) (hB := hB) (M := M)
  haveI : ∀ q, ((GlobalTransferRecovery.commonDual i s₀ B M v).X q).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.common_dual_qc M (Survivor.coefficient i s₀)
      (Survivor.chart (R := R)) B (n+2) hB v
  haveI := ProjectiveRefinement.DualMap.left_quasiIso M (Survivor.coefficient i s₀)
    (Survivor.chart (R := R)) B (n+2) hB v
  exact LocalClass.map i s₀ hbase B hB U hU a t hat ≫
    (Principal.AdditiveSections.forgetScalars U).map
      (Principal.RelativeTransfer.map U hU (PrincipalPoint.Fraction.family U t) (n+1)
        (GlobalTransferRecovery.left i s₀ B M v)
        (GlobalTransferRecovery.right i s₀ B M v))

def native : nativeGroup B (Survivor.coefficient i s₀) ⟶ nativeGroup B M :=
  Projective.TotalUnitCoordinates.nativeMap M (Survivor.coefficient i s₀) B n
    (Fintype.card_fin (n+2)) hB v

def nativeTransfer : nativeGroup B (Survivor.coefficient i s₀) ⟶ nativeGroup B M := by
  haveI : ∀ q : ℕ, ((GlobalTransferRecovery.coefficientDual B M).X q).IsQuasicoherent :=
    coefficient_quasicoherent (B := B) (hB := hB) (M := M)
  haveI : ∀ q, ((GlobalTransferRecovery.commonDual i s₀ B M v).X q).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.common_dual_qc M (Survivor.coefficient i s₀)
      (Survivor.chart (R := R)) B (n+2) hB v
  haveI := ProjectiveRefinement.DualMap.left_quasiIso M (Survivor.coefficient i s₀)
    (Survivor.chart (R := R)) B (n+2) hB v
  exact IntrinsicOrdered.CechTransferCoordinates.Intrinsic.nativeMap π V haV (n+1)
    (GlobalTransferRecovery.left i s₀ B M v)
    (GlobalTransferRecovery.right i s₀ B M v)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalSectionData.Class
