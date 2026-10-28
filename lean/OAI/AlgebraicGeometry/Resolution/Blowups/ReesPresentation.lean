import OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveClosedImmersion
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Rees Presentation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ReesPresentation

noncomputable section

/-! Polynomial presentations and relative projective embeddings of affine blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Construction

universe u

variable {R ι : Type u} [CommRing R] (I : Ideal R) (a : ι → I)

/-- A generating family for the ideal gives algebra generators for its Rees algebra. -/
theorem reesFamily_adjoin (hgen : Submodule.span R (Set.range a) = ⊤) :
    Algebra.adjoin R (Set.range (fun i => Blowup.Charts.Construction.reesGenerator I (a i))) = ⊤ := by
  let C := Algebra.adjoin R (Set.range (fun i => Blowup.Charts.Construction.reesGenerator I (a i)))
  have hspan : Submodule.span R (Set.range a) ≤ C.toSubmodule.comap (ReesMap.Construction.reesGeneratorLinear I) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Algebra.subset_adjoin ⟨i, rfl⟩
  rw [hgen] at hspan
  apply top_le_iff.mp
  rw [← Blowup.Charts.Construction.reesGenerators_adjoin I]
  apply Algebra.adjoin_le
  rintro _ ⟨b, rfl⟩
  exact hspan (Submodule.mem_top : b ∈ (⊤ : Submodule R I))

/-- Evaluation at degree-one Rees generators preserves total degree. -/
theorem reesPolynomialEval_mem {n : ℕ} (p : MvPolynomial ι R)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule ι R n) :
    MvPolynomial.aeval (fun i => Blowup.Charts.Construction.reesGenerator I (a i)) p ∈ ReesGrading.Construction.reesGrade I n := by
  classical
  rw [← p.support_sum_monomial_coeff, map_sum]
  apply Submodule.sum_mem
  intro d hd
  rw [MvPolynomial.aeval_monomial, Finsupp.prod]
  have hprod := SetLike.prod_pow_mem_graded (ReesGrading.Construction.reesGrade I) (fun _ : ι => (1 : ℕ))
    (fun i => Blowup.Charts.Construction.reesGenerator I (a i)) d (F := d.support) (fun i _ => Blowup.Charts.Construction.reesGenerator_mem I (a i))
  have hconst : algebraMap R (reesAlgebra I) (AddMonoidAlgebra.coeff (p) (d)) ∈ ReesGrading.Construction.reesGrade I 0 :=
    SetLike.algebraMap_mem_graded (ReesGrading.Construction.reesGrade I) _
  rw [(show p.IsHomogeneous n from hp).degree_eq_sum_deg_support hd]
  simpa only [zero_add, smul_eq_mul, mul_one] using SetLike.mul_mem_graded hconst hprod

/-- The graded polynomial presentation determined by an ideal generating family. -/
def reesPolynomialPresentation :
    MvPolynomial.homogeneousSubmodule ι R →+*ᵍ ReesGrading.Construction.reesGrade I where
  __ := (MvPolynomial.aeval (fun i => Blowup.Charts.Construction.reesGenerator I (a i))).toRingHom
  map_mem := reesPolynomialEval_mem I a _

theorem reesPolynomialPresentation_surjective (hgen : Submodule.span R (Set.range a) = ⊤) :
    Function.Surjective (reesPolynomialPresentation I a) := by
  change Function.Surjective (MvPolynomial.aeval (fun i => Blowup.Charts.Construction.reesGenerator I (a i)))
  rw [← AlgHom.range_eq_top, MvPolynomial.aeval_range]
  exact reesFamily_adjoin I a hgen

/-- A generating family embeds the actual affine blowup as a closed subscheme
of projective space over the coefficient ring. -/
def affineBlowupProjectiveEmbedding (hgen : Submodule.span R (Set.range a) = ⊤) :
    ReesGrading.Construction.affineBlowup I ⟶ Proj (MvPolynomial.homogeneousSubmodule ι R) :=
  ProjectiveClosedImmersion.Construction.projClosedMap (reesPolynomialPresentation I a) (reesPolynomialPresentation_surjective I a hgen)

instance affineBlowupProjectiveEmbedding_isClosedImmersion
    (hgen : Submodule.span R (Set.range a) = ⊤) :
    IsClosedImmersion (affineBlowupProjectiveEmbedding I a hgen) :=
  ProjectiveClosedImmersion.Construction.projClosedMap_isClosedImmersion _ _

/-- The structural map of polynomial projective space over the coefficient ring. -/
def polynomialProjToSpec : Proj (MvPolynomial.homogeneousSubmodule ι R) ⟶ Spec (.of R) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule ι R) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial.homogeneousSubmodule ι R 0)))

/-- The projective embedding of the affine blowup is over its original affine base. -/
theorem affineBlowupProjectiveEmbedding_over (hgen : Submodule.span R (Set.range a) = ⊤) :
    affineBlowupProjectiveEmbedding I a hgen ≫ polynomialProjToSpec = ReesGrading.Construction.affineBlowupToSpec I := by
  unfold affineBlowupProjectiveEmbedding ProjectiveClosedImmersion.Construction.projClosedMap polynomialProjToSpec ReesGrading.Construction.affineBlowupToSpec
  rw [← Category.assoc, Blowup.BaseOpen.Construction.projMap_toSpecZero, Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  apply Subtype.ext
  exact MvPolynomial.aeval_C (fun i => Blowup.Charts.Construction.reesGenerator I (a i)) r

/-- Over a Noetherian affine base, the blowup has an actual closed embedding
into a polynomial projective space with finitely many coordinates. -/
theorem affineBlowup_exists_finite_projectiveEmbedding [IsNoetherianRing R] :
    ∃ (s : Finset I)
      (i : ReesGrading.Construction.affineBlowup I ⟶ Proj (MvPolynomial.homogeneousSubmodule s R)),
      IsClosedImmersion i ∧ i ≫ polynomialProjToSpec = ReesGrading.Construction.affineBlowupToSpec I := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := R) (M := I))
  have hgen : Submodule.span R (Set.range (fun x : s => (x.val : I))) = ⊤ := by
    have hrange : Set.range (fun x : s => (x.val : I)) = (s : Set I) := by
      ext x
      exact ⟨fun ⟨y, h⟩ => h ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
    rw [hrange]
    exact hs
  exact ⟨s, affineBlowupProjectiveEmbedding I (fun x : s => x.val) hgen,
    affineBlowupProjectiveEmbedding_isClosedImmersion I _ hgen,
    affineBlowupProjectiveEmbedding_over I _ hgen⟩

end Construction

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ReesPresentation
