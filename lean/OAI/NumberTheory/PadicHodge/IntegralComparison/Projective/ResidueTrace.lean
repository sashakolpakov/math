import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentTop
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentCount
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-! # Residue Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ResidueTrace

noncomputable section

/-! The canonical full-negative Laurent coefficient gives the trace
isomorphism on the original top Čech cohomology of O(-d-1) on projective
d-space. This construction works over an arbitrary commutative ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (σ : Type) [Fintype σ]

abbrev TopExponent :=
  {e : OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ (-(Fintype.card σ : ℤ)) //
    e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))}

def topExponent : TopExponent.{u} σ :=
  ⟨⟨Finsupp.equivFunOnFinite.symm (fun _ : σ => (-1 : ℤ)), by
      simp [Finsupp.degree_eq_sum]⟩, by
    apply Set.eq_univ_of_forall
    intro i
    change (-1 : ℤ) < 0
    norm_num⟩

theorem topExponent_apply (i : σ) : (topExponent.{u} σ).val.val i = -1 := by
  simp [topExponent]

def fullNegativeZeroWeightEquiv :
    OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentCount.MvPolynomial.FullNegativeLaurentWeight σ (-(Fintype.card σ : ℤ)) ≃
      {a : σ →₀ ℕ // Finsupp.degree a = 0} := by
  simpa only [Nat.cast_zero, neg_zero, zero_sub] using
    (OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentCount.MvPolynomial.fullNegativeLaurentWeightEquivDegree (σ := σ) 0)

theorem topExponent_unique (e : TopExponent.{u} σ) : e = topExponent.{u} σ := by
  let : Subsingleton {a : σ →₀ ℕ // Finsupp.degree a = 0} :=
    ⟨fun a b => Subtype.ext (((Finsupp.degree_eq_zero_iff a.val).mp a.property).trans
      ((Finsupp.degree_eq_zero_iff b.val).mp b.property).symm)⟩
  let : Subsingleton (OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentCount.MvPolynomial.FullNegativeLaurentWeight σ (-(Fintype.card σ : ℤ))) :=
    (fullNegativeZeroWeightEquiv σ).injective.subsingleton
  let : Subsingleton (TopExponent.{u} σ) :=
    (OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentCount.MvPolynomial.liftedFullNegativeLaurentWeightEquiv.{u} (σ := σ) (-(Fintype.card σ : ℤ))).injective.subsingleton
  exact Subsingleton.elim _ _

variable (R : Type u) [CommRing R]

def coefficientsEquiv :
    (TopExponent.{u} σ → Γ(Spec (CommRingCat.of R), ⊤)) ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
      Γ(Spec (CommRingCat.of R), ⊤) where
  toFun f := f (topExponent σ)
  invFun r := fun _ => r
  left_inv f := funext (fun e => congrArg f (topExponent_unique σ e).symm)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coefficientsEquiv_apply (f : TopExponent.{u} σ → Γ(Spec (CommRingCat.of R), ⊤)) :
    coefficientsEquiv σ R f = f (topExponent σ) := rfl

def coefficientsEquivCard (m : ℕ) (hm : Fintype.card σ = m) :
    ({e : OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ (-(m : ℤ)) //
        e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))} → Γ(Spec (CommRingCat.of R), ⊤))
      ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)] Γ(Spec (CommRingCat.of R), ⊤) := by
  subst m
  exact coefficientsEquiv σ R

def laurentTrace (n : ℕ) (j : Fin (n + 2)) :
    (OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j (-((n + 2 : ℕ) : ℤ))).homology (n + 1)
      ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)] Γ(Spec (CommRingCat.of R), ⊤) := by
  let e := OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentTop.MvPolynomial.coordinateHomogeneousLaurentTopHomologyEquivCoefficients
    (R := R) j (-((n + 2 : ℕ) : ℤ)) n (by simp)
  exact e.trans (coefficientsEquivCard (Fin (n + 2)) R (n + 2) (by simp))

def trace (n : ℕ) (j : Fin (n + 2)) :
    (OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
      (OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2)))
      (OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j (-((n + 2 : ℕ) : ℤ)))
      (OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n + 2)))).homology (n + 1)
        ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)] Γ(Spec (CommRingCat.of R), ⊤) :=
  (HomologicalComplex.homologyMapIso
    ((OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplexIso (R := R) j (-((n + 2 : ℕ) : ℤ))) ≪≫
      (OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplexIso (R := R) j (-((n + 2 : ℕ) : ℤ))))
    (n + 1)).toLinearEquiv.trans (laurentTrace R n j)

theorem trace_surjective (n : ℕ) (j : Fin (n + 2)) : Function.Surjective (trace R n j) :=
  (trace R n j).surjective

theorem trace_injective (n : ℕ) (j : Fin (n + 2)) : Function.Injective (trace R n j) :=
  (trace R n j).injective

/-- The same residue trace on the original sheaf cohomology, through
the actual affine-cover Čech comparison. -/
def sheafTrace (n : ℕ) (j : Fin (n + 2)) :
    letI := OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule
      (OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2)))
      (OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j (-((n + 2 : ℕ) : ℤ))) (n + 1)
    OAI.AlgebraicGeometry.SheafCohomology.AffineH.Projective.H (OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j (-((n + 2 : ℕ) : ℤ))) (n + 1)
      ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)] Γ(Spec (CommRingCat.of R), ⊤) := by
  letI := OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule
    (OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2)))
    (OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j (-((n + 2 : ℕ) : ℤ))) (n + 1)
  let : (OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j (-((n + 2 : ℕ) : ℤ))).IsQuasicoherent :=
    OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent
      (OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := R) j (-((n + 2 : ℕ) : ℤ)))
  exact (OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees.orderedBaseCechHomologyAffineHLinearEquiv
    (OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2)))
    (OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j (-((n + 2 : ℕ) : ℤ)))
    (OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n + 2)))
    (TopologicalSpace.IsOpenCover.mk (OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R)))
    (OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R)) (n + 1)).symm.trans (trace R n j)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ResidueTrace
