import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Duality
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Vanishing
import OAI.NumberTheory.PadicHodge.IntegralComparison.KernelTowerCechHomology

/-! # Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Cohomology

noncomputable section

/-! The top-cohomology complex of the actual negative-twist resolution
computes the lower native Čech cohomology of the original coherent sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.NegativeResolution OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Duality
  Vanishing

variable (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType]
  (j : σ) (B : ℕ)

private instance tower_object_quasicoherent (i : ℕ) :
    ((Projective.NegativeResolution.tower M j B).object i).IsQuasicoherent :=
  inferInstanceAs ((Projective.NegativeResolution.state M j B i).module.IsQuasicoherent)

private instance tower_term_quasicoherent (i : ℕ) :
    ((Projective.NegativeResolution.tower M j B).term i).IsQuasicoherent :=
  Duality.term_quasicoherent M j B i

def zeroIso (n : ℕ) (hn : Fintype.card σ = n + 2) :
    (Duality.topComplex M j B n).homology 0 ≅
      (Vanishing.cohomology (R := R) (σ := σ) (n + 1)).obj M :=
  KernelTowerCechHomology.zeroIso (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R))
    (Projective.NegativeResolution.tower M j B) (n + 1) (by simpa using hn.le)

def positiveIso (hB : 0 < B) (q i : ℕ) (hn : Fintype.card σ = q + i + 2) :
    (Duality.topComplex M j B (q + i)).homology (i + 1) ≅
      (Vanishing.cohomology (R := R) (σ := σ) q).obj M := by
  letI : Nontrivial σ := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact KernelTowerCechHomology.shiftedPositiveIso (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R))
    (Projective.NegativeResolution.tower M j B) q i (by simpa using hn.le)
    (fun r hr k => Vanishing.term_isZero M j B hB k r (by omega))

def comparisonIso (hB : 0 < B) (n : ℕ) (hn : Fintype.card σ = n + 2)
    (d : ℕ) (hd : d ≤ n + 1) :
    (Duality.topComplex M j B n).homology d ≅
      (Vanishing.cohomology (R := R) (σ := σ) (n + 1 - d)).obj M := by
  cases d with
  | zero => exact zeroIso M j B n hn
  | succ i =>
    have hi : i ≤ n := by omega
    have hi' : n - i + i = n := Nat.sub_add_cancel hi
    have hcard : Fintype.card σ = n - i + i + 2 := by omega
    simpa only [hi', Nat.add_sub_add_right] using positiveIso M j B hB (n - i) i hcard

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Cohomology
