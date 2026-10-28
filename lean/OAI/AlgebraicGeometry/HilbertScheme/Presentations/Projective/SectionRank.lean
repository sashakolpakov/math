import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BaseLinearSectionIso
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.TwistSectionRank
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.TwistRankRigidity

/-! # Section Rank -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.SectionRank

noncomputable section

/-! A base-linear section rank for actual projective module sheaves,
invariant under module isomorphism and base-preserving scheme automorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K] {n : ℕ}

def projectiveSectionRank (M : (Proj (Hilbert.Polynomial.GradedHilbert.grading K n)).Modules) : ℕ :=
  letI := Module.compHom Γ(M, ⊤) (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) (σ := Fin (n + 1))).appTop.hom
  Module.finrank Γ(Spec (.of K), ⊤) Γ(M, ⊤)

theorem projectiveSectionRank_iso {M N : (Proj (Hilbert.Polynomial.GradedHilbert.grading K n)).Modules} (e : M ≅ N) :
    projectiveSectionRank K M = projectiveSectionRank K N := by
  let := Module.compHom Γ(M, ⊤) (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) (σ := Fin (n + 1))).appTop.hom
  let := Module.compHom Γ(N, ⊤) (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) (σ := Fin (n + 1))).appTop.hom
  exact (BaseLinearSectionIso.baseLinearSectionIso (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) (σ := Fin (n + 1))) e).finrank_eq

theorem projectiveSectionRank_pullback
    (e : Proj (Hilbert.Polynomial.GradedHilbert.grading K n) ≅ Proj (Hilbert.Polynomial.GradedHilbert.grading K n))
    (he : e.hom ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)
    (M : (Proj (Hilbert.Polynomial.GradedHilbert.grading K n)).Modules) :
    projectiveSectionRank K ((Scheme.Modules.pullback e.hom).obj M) = projectiveSectionRank K M := by
  let := Module.compHom Γ(M, ⊤) (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) (σ := Fin (n + 1))).appTop.hom
  let := Module.compHom Γ((Scheme.Modules.pullback e.hom).obj M, ⊤)
    (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) (σ := Fin (n + 1))).appTop.hom
  exact (BaseLinearSectionPullback.baseLinearSectionPullbackEquiv SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ e he M).finrank_eq.symm

theorem projectiveSectionRank_twist_nat (j : Fin (n + 1)) (d : ℕ) :
    projectiveSectionRank K (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) j (d : ℤ)) = (d + n).choose n :=
  TwistSectionRank.projectiveTwistSections_finrank K j d

theorem projectiveSectionRank_twist_neg (hn : 0 < n) (j : Fin (n + 1)) (d : ℤ) (hd : d < 0) :
    projectiveSectionRank K (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) j d) = 0 := by
  let := (TwistSectionRank.specFieldSectionRing_isField K).toField
  let := Module.compHom Γ(SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) j d, ⊤)
    (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) (σ := Fin (n + 1))).appTop.hom
  let := TwistSectionRank.projectiveTwistSections_subsingleton_of_neg K hn j d hd
  exact Module.finrank_zero_of_subsingleton

theorem projectiveSectionRank_twist_eq_dimension (hn : 0 < n) (j : Fin (n + 1)) (d : ℤ)
    (hd : projectiveSectionRank K (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) j d) = n + 1) : d = 1 := by
  by_cases hnonneg : 0 ≤ d
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hnonneg
    rw [projectiveSectionRank_twist_nat] at hd
    have ha := (TwistRankRigidity.projectiveTwistRank_eq_dimension_iff n hn a).mp hd
    exact_mod_cast ha
  · rw [projectiveSectionRank_twist_neg K hn j d (lt_of_not_ge hnonneg)] at hd
    omega

theorem projectiveSectionRank_twist_eq_natDegree (hn : 0 < n) (j : Fin (n + 1)) (d : ℤ) (m : ℕ)
    (hd : projectiveSectionRank K (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) j d) = (m + n).choose n) : d = (m : ℤ) := by
  by_cases hnonneg : 0 ≤ d
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hnonneg
    rw [projectiveSectionRank_twist_nat] at hd
    exact_mod_cast (TwistRankRigidity.projectiveTwistRank_strictMono n hn).injective hd
  · rw [projectiveSectionRank_twist_neg K hn j d (lt_of_not_ge hnonneg)] at hd
    have hp : 0 < (m + n).choose n := Nat.choose_pos (Nat.le_add_left n m)
    omega

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.SectionRank
