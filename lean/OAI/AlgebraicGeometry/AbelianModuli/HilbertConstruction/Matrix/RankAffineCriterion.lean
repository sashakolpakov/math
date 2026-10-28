import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.CokernelLocalization
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Matrix.FlatRankLocus

/-! # Rank Affine Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.RankAffineCriterion

noncomputable section

/-! The represented matrix rank locus has the expected criterion on affine tests: flatness and constant rank of the actual coefficient-matrix cokernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian

universe u

variable {ι μ ν : Type u} [Fintype ι] [Fintype μ] [Fintype ν]
variable [DecidableEq ι] [DecidableEq μ] [DecidableEq ν]

omit [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν] in
theorem matrixPivotCondition_ringEquiv {R T U : Type u} [CommRing R] [CommRing T] [CommRing U]
    (A : Matrix ν μ R) (a : ι → μ) (b : ι → ν) (φ : R →+* T) (e : T ≃+* U) :
    HilbertScheme.Presentations.MatrixPivot.Locus.Grassmannian.matrixPivotCondition (A.submatrix b a) (A.submatrix b id) (A.submatrix id a) A
      (e.toRingHom.comp φ) ↔
    HilbertScheme.Presentations.MatrixPivot.Locus.Grassmannian.matrixPivotCondition (A.submatrix b a) (A.submatrix b id) (A.submatrix id a) A φ := by
  simp only [HilbertScheme.Presentations.MatrixPivot.Locus.Grassmannian.matrixPivotCondition, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, isUnit_map_iff]
  exact and_congr_right (fun _ => forall_congr' (fun p => e.map_eq_zero_iff))

variable {S : Scheme.{u}} (M : Over S) (A : Matrix ν μ Γ(M.left, ⊤))
variable (R : CommRingCat.{u}) {f : Spec R ⟶ S} (x : Over.mk f ⟶ M)

def affineMatrixCoefficients : Matrix ν μ R :=
  A.map ((Scheme.ΓSpecIso R).hom.hom.comp x.left.appTop.hom)

theorem affineMatrix_stalk_coefficients (p : PrimeSpectrum R) :
    (Spec.stalkIso R p).hom.hom.comp
        (((Spec R).presheaf.Γgerm p).hom.comp x.left.appTop.hom) =
      (algebraMap R (Localization.AtPrime p.asIdeal)).comp
        ((Scheme.ΓSpecIso R).hom.hom.comp x.left.appTop.hom) := by
  ext s
  exact ConcreteCategory.congr_hom (Spec.germ_stalkMapIso_hom (R := R) p) (x.left.appTop s)

theorem matrixRank_affine_iff :
    HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.MatrixCokernelFlatRank (ι := ι) M A x ↔
      (Module.Flat R ((ν → R) ⧸ (Matrix.toLin' (affineMatrixCoefficients M A R x)).range) ∧
        ∀ p, Module.rankAtStalk (R := R)
          ((ν → R) ⧸ (Matrix.toLin' (affineMatrixCoefficients M A R x)).range) p +
            Fintype.card ι = Fintype.card ν) := by
  rw [HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.matrixCokernelFlatRank_iff_stalk,
    CokernelLocalization.matrixCokernel_flatRank_iff_localizations]
  apply forall_congr'
  intro p
  rw [HilbertScheme.Presentations.Local.FixedRankCokernel.Grassmannian.local_cokernel_flat_fixed_rank_iff (ι := ι)]
  change (∃ ab : HilbertScheme.Presentations.MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν,
    HilbertScheme.Presentations.MatrixPivot.Locus.Grassmannian.matrixPivotCondition (A.submatrix ab.2 ab.1) (A.submatrix ab.2 id)
      (A.submatrix id ab.1) A (((Spec R).presheaf.Γgerm p).hom.comp x.left.appTop.hom)) ↔ _
  constructor
  · rintro ⟨⟨a, b⟩, h⟩
    have he := (matrixPivotCondition_ringEquiv A a b _
      (Spec.stalkIso R p).commRingCatIsoToRingEquiv).mpr h
    change HilbertScheme.Presentations.MatrixPivot.Locus.Grassmannian.matrixPivotCondition _ _ _ _
      ((Spec.stalkIso R p).hom.hom.comp (((Spec R).presheaf.Γgerm p).hom.comp x.left.appTop.hom)) at he
    rw [affineMatrix_stalk_coefficients M R x p] at he
    have hp := (HilbertScheme.Presentations.MatrixPivot.Condition.Grassmannian.fullMatrixPivotCondition_iff A a b _).mp he
    exact ⟨a, b, hp⟩
  · rintro ⟨a, b, h⟩
    refine ⟨⟨a, b⟩, ?_⟩
    apply (matrixPivotCondition_ringEquiv A a b _
      (Spec.stalkIso R p).commRingCatIsoToRingEquiv).mp
    change HilbertScheme.Presentations.MatrixPivot.Locus.Grassmannian.matrixPivotCondition _ _ _ _
      ((Spec.stalkIso R p).hom.hom.comp (((Spec R).presheaf.Γgerm p).hom.comp x.left.appTop.hom))
    rw [affineMatrix_stalk_coefficients M R x p]
    exact (HilbertScheme.Presentations.MatrixPivot.Condition.Grassmannian.fullMatrixPivotCondition_iff A a b _).mpr h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.RankAffineCriterion
