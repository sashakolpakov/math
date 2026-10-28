import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedModuleLocalization
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.GradedAction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Exactness

/-! # Iterated Localized Degrees -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedLocalizedDegrees.GradedModules

noncomputable section

/-! Iterated homogeneous module localizations identify their actual degree pieces with localization at the product. -/

open DirectSum

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule R M) [SetLike.GradedSMul 𝒜 ℳ]

theorem iteratedAwayModuleEquiv_homogeneous (a b : A) (α β : ℤ)
    (ha : a ∈ 𝒜 α) (hb : b ∈ 𝒜 β) (d : ℤ) (x : Presentations.Module.Fractions.GradedModules.AwayModule b (Presentations.Module.Fractions.GradedModules.AwayModule a M))
    (hx : x ∈ Localized.DegreePieces.GradedModules.localizedDegreePiece (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ a α) b β d) :
    IteratedModuleLocalization.GradedModules.iteratedAwayModuleEquiv M a b x ∈ Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ (a * b) (α + β) d := by
  let := Localized.GradedAction.GradedModules.localizedDegree_gradedSMul 𝒜 ℳ a α ha
  obtain ⟨j, y, hy, rfl⟩ := (Localized.DegreePieces.GradedModules.mem_localizedDegreePiece_iff 𝒜 (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ a α) b β hb d x).mp hx
  obtain ⟨i, m, hm, rfl⟩ := (Localized.DegreePieces.GradedModules.mem_localizedDegreePiece_iff 𝒜 ℳ a α ha (d + (j : ℤ) * β) y).mp hy
  have hpa : a ^ j ∈ 𝒜 ((j : ℤ) * α) := by simpa only [nsmul_eq_mul] using SetLike.pow_mem_graded j ha
  have hpb : b ^ i ∈ 𝒜 ((i : ℤ) * β) := by simpa only [nsmul_eq_mul] using SetLike.pow_mem_graded i hb
  have hmem := SetLike.GradedSMul.smul_mem hpa (SetLike.GradedSMul.smul_mem hpb hm)
  have he : (j : ℤ) * α + ((i : ℤ) * β + ((d + (j : ℤ) * β) + (i : ℤ) * α)) =
      d + ((i + j : ℕ) : ℤ) * (α + β) := by push_cast; ring
  have hm' : a ^ j • (b ^ i • m) ∈ ℳ (d + ((i + j : ℕ) : ℤ) * (α + β)) := he ▸ hmem
  have hfrac : Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) b j (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a i m) =
      Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) b (i + j)
        (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a (i + j) (a ^ j • (b ^ i • m))) :=
    (IteratedModuleFractions.GradedModules.iteratedModuleFraction_common M a b i j m).symm
  rw [hfrac]
  change IteratedModuleLocalization.GradedModules.iteratedAwayToProduct M a b
    (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) b (i + j) (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := A) a (i + j) (a ^ j • (b ^ i • m)))) ∈ _
  rw [IteratedModuleLocalization.GradedModules.iteratedAwayToProduct_double_fraction]
  exact Localized.DegreePieces.GradedModules.moduleFractionMap_mem_degree ℳ (a * b) (α + β) d (i + j) (a ^ j • (b ^ i • m)) hm'

variable [Decomposition ℳ]

def iteratedLocalizedDegreeEquiv (a b : A) (α β : ℤ) (ha : a ∈ 𝒜 α) (hb : b ∈ 𝒜 β) (d : ℤ) :
    Localized.DegreePieces.GradedModules.localizedDegreePiece (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ a α) b β d ≃ₗ[R]
      Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ (a * b) (α + β) d := by
  let := Localized.Grading.GradedModules.localizedDegreeDecomposition 𝒜 ℳ a α ha
  let := Localized.GradedAction.GradedModules.localizedDegree_gradedSMul 𝒜 ℳ a α ha
  let := Localized.Grading.GradedModules.localizedDegreeDecomposition 𝒜 (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ a α) b β hb
  let := Localized.Grading.GradedModules.localizedDegreeDecomposition 𝒜 ℳ (a * b) (α + β) (SetLike.mul_mem_graded ha hb)
  let E := (IteratedModuleLocalization.GradedModules.iteratedAwayModuleEquiv M a b).restrictScalars R
  let f := Graded.Exactness.GradedModules.degreeMap (Localized.DegreePieces.GradedModules.localizedDegreePiece (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ a α) b β)
    (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ (a * b) (α + β)) E.toLinearMap
    (iteratedAwayModuleEquiv_homogeneous 𝒜 ℳ a b α β ha hb) d
  exact LinearEquiv.ofBijective f ⟨by
    intro x y hxy
    have hval := congrArg (fun z : Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ (a * b) (α + β) d => z.val) hxy
    change E x.val = E y.val at hval
    exact Subtype.ext (E.injective hval),
    Graded.Exactness.GradedModules.degreeMap_surjective _ _ E.toLinearMap
      (iteratedAwayModuleEquiv_homogeneous 𝒜 ℳ a b α β ha hb) E.surjective d⟩

theorem iteratedAwayModuleEquiv_degree (a b : A) (α β : ℤ) (ha : a ∈ 𝒜 α) (hb : b ∈ 𝒜 β) (d : ℤ) :
    (Localized.DegreePieces.GradedModules.localizedDegreePiece (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ a α) b β d).map
      ((IteratedModuleLocalization.GradedModules.iteratedAwayModuleEquiv M a b).restrictScalars R).toLinearMap =
        Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ (a * b) (α + β) d := by
  apply Submodule.ext
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact iteratedAwayModuleEquiv_homogeneous 𝒜 ℳ a b α β ha hb d y hy
  · intro hx
    let E := iteratedLocalizedDegreeEquiv 𝒜 ℳ a b α β ha hb d
    refine Submodule.mem_map.mpr ⟨(E.symm ⟨x, hx⟩).val, (E.symm ⟨x, hx⟩).property, ?_⟩
    exact congrArg (fun z : Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ (a * b) (α + β) d => z.val) (E.apply_symm_apply ⟨x, hx⟩)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedLocalizedDegrees.GradedModules
