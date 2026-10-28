import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionFunctoriality

/-! # Torsion Embedding -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.TorsionEmbedding.Construction

noncomputable section

/-!
The level-two kernel uses the same étale q-torsion plane, embedded in
q²-torsion. The scheme below is built by the zero-fiber universal property;
the source subgroup is unchanged and remains killed by q on all tests.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {g : ℕ} {S : Scheme.{u}} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem torsionInclusion_pow_of_dvd {m n : ℕ} (hmn : m ∣ n) :
    A.torsionInclusion m ^ n = 1 := by
  obtain ⟨k, rfl⟩ := hmn
  rw [pow_mul, A.torsionInclusion_pow, one_pow]

/-- The canonical closed embedding of m-torsion in n-torsion for m | n. -/
def torsionLevelEmbedding {m n : ℕ} (hmn : m ∣ n) :
    A.torsionScheme m ⟶ A.torsionScheme n :=
  (A.torsionSchemePointsEquiv n (A.torsionScheme m)).symm
    ⟨A.torsionInclusion m, torsionInclusion_pow_of_dvd A hmn⟩

theorem torsionLevelEmbedding_inclusion {m n : ℕ} (hmn : m ∣ n) :
    torsionLevelEmbedding A hmn ≫ A.torsionInclusion n = A.torsionInclusion m :=
  congrArg (fun x : A.torsionPoints n (A.torsionScheme m) => x.val)
    ((A.torsionSchemePointsEquiv n (A.torsionScheme m)).apply_symm_apply _)

instance torsionLevelEmbedding_mono {m n : ℕ} (hmn : m ∣ n) :
    Mono (torsionLevelEmbedding A hmn) := by
  have : Mono (torsionLevelEmbedding A hmn ≫ A.torsionInclusion n) := by
    rw [torsionLevelEmbedding_inclusion]
    infer_instance
  exact mono_of_mono (torsionLevelEmbedding A hmn) (A.torsionInclusion n)

instance torsionLevelEmbedding_closed {m n : ℕ} (hmn : m ∣ n) :
    IsClosedImmersion (torsionLevelEmbedding A hmn).left := by
  have h := congrArg (fun f => f.left) (torsionLevelEmbedding_inclusion A hmn)
  have : IsClosedImmersion
      ((torsionLevelEmbedding A hmn).left ≫ (A.torsionInclusion n).left) :=
    (congrArg IsClosedImmersion h).mpr
      (inferInstanceAs (IsClosedImmersion (A.torsionInclusion m).left))
  exact IsClosedImmersion.of_comp _ (A.torsionInclusion n).left

/-- Any chosen q-torsion subgroup, in particular the active étale plane,
is placed inside q²-torsion without replacing its source scheme. -/
def qTorsionAtLevelTwo (q : ℕ) {H : Over S} (i : H ⟶ A.torsionScheme q) :
    H ⟶ A.torsionScheme (q ^ 2) :=
  i ≫ torsionLevelEmbedding A (show q ∣ q ^ 2 by exact ⟨q, pow_two q⟩)

theorem qTorsionAtLevelTwo_inclusion (q : ℕ) {H : Over S}
    (i : H ⟶ A.torsionScheme q) :
    qTorsionAtLevelTwo A q i ≫ A.torsionInclusion (q ^ 2) = i ≫ A.torsionInclusion q := by
  exact (Category.assoc _ _ _).trans
    (congrArg (fun f => i ≫ f) (torsionLevelEmbedding_inclusion A _))

theorem qTorsionAtLevelTwo_killedByQ (q : ℕ) {H : Over S}
    (i : H ⟶ A.torsionScheme q) (T : Over S) (x : T ⟶ H) :
    (x ≫ qTorsionAtLevelTwo A q i ≫ A.torsionInclusion (q ^ 2)) ^ q = 1 := by
  have h : (x ≫ i ≫ A.torsionInclusion q) ^ q = 1 := by
    rw [← Category.assoc, ← MonObj.comp_pow, A.torsionInclusion_pow, MonObj.comp_one]
  exact (congrArg (fun f => (x ≫ f) ^ q) (qTorsionAtLevelTwo_inclusion A q i)).trans h

instance qTorsionAtLevelTwo_mono (q : ℕ) {H : Over S}
    (i : H ⟶ A.torsionScheme q) [Mono i] : Mono (qTorsionAtLevelTwo A q i) :=
  inferInstanceAs (Mono (i ≫ torsionLevelEmbedding A _))

instance qTorsionAtLevelTwo_closed (q : ℕ) {H : Over S}
    (i : H ⟶ A.torsionScheme q) [IsClosedImmersion i.left] :
    IsClosedImmersion (qTorsionAtLevelTwo A q i).left :=
  inferInstanceAs (IsClosedImmersion (i.left ≫ (torsionLevelEmbedding A _).left))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.TorsionEmbedding.Construction
