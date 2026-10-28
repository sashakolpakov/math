import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.NegativeResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.NegativeTwistVanishing
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoproductVanishing
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopCechRightExact

/-! # Vanishing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Vanishing

noncomputable section

/-! Each term of a sufficiently negative projective resolution has native
Čech cohomology concentrated in the top projective degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ] [Nontrivial σ]

attribute [local instance] MvPolynomial.gradedAlgebra

local instance (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

abbrev cohomology (q : ℕ) :=
  TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) q

theorem twist_isZero (j : σ) (d : ℕ) (hd : 0 < d) (q : ℕ)
    (hq : q + 1 ≠ Fintype.card σ) :
    IsZero ((cohomology (R := R) (σ := σ) q).obj
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j d)) := by
  cases d with
  | zero => omega
  | succ d =>
    exact Intrinsic.NegativeTwistVanishing.isZero_homology (R := R) j (.negSucc d)
      (Int.negSucc_lt_zero d) q hq

theorem coproduct_isZero {I : Type} [Fintype I] (j : σ) (d : I → ℕ)
    (hd : ∀ i, 0 < d i) (q : ℕ) (hq : q + 1 ≠ Fintype.card σ) :
    IsZero ((cohomology (R := R) (σ := σ) q).obj
      (∐ fun i : I => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i))) :=
  Finite.CoproductVanishing.isZero_image _ _
    (fun i => twist_isZero j (d i) (hd i) q hq)

variable [IsNoetherianRing R]

theorem term_isZero
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : σ) (B : ℕ) (hB : 0 < B) (n q : ℕ) (hq : q + 1 ≠ Fintype.card σ) :
    IsZero ((cohomology (R := R) (σ := σ) q).obj
      ((Projective.NegativeResolution.complex M j B).X n)) := by
  let Q := Projective.NegativeResolution.presentation
    (Projective.NegativeResolution.state M j B n).module j B
  exact (coproduct_isZero j Q.degree (fun i => lt_of_lt_of_le hB (Q.degree_bound i)) q hq).of_iso
    ((cohomology (R := R) (σ := σ) q).mapIso
      (Projective.NegativeResolution.termIso M j B n))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Vanishing
