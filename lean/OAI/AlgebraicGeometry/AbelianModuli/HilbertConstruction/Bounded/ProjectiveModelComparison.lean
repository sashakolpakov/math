import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveQuasiIsoLift

/-! # Projective Model Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.ProjectiveModelComparison

noncomputable section

/-! Bounded projective models of nonnegative cochain complexes admit
actual comparison maps commuting up to homotopy with a quasi-isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

theorem boundedProjective_exists_lift
    {K L M : CochainComplex C ℕ} [∀ i, Projective (K.X i)]
    (N : ℕ) (hN : ∀ i, N ≤ i → IsZero (K.X i))
    (p : L ⟶ M) [QuasiIso p] (f : K ⟶ M) :
    ∃ g : K ⟶ L, Nonempty (Homotopy (g ≫ p) f) := by
  let e := ComplexShape.embeddingUpNat
  have : _root_.CochainComplex.IsStrictlyLE (K.extend e) (N : ℤ) := by
    apply (_root_.CochainComplex.isStrictlyLE_iff _ _).mpr
    intro i hi
    have hi₀ : 0 ≤ i := by omega
    have hi' : e.f i.toNat = i := Int.toNat_of_nonneg hi₀
    exact (hN i.toNat (by omega)).of_iso (K.extendXIso e hi')
  have : ProjectiveBasic.CochainComplex.IsKProjective (K.extend e) :=
    ProjectiveBasic.CochainComplex.isKProjective_of_projective _ (N : ℤ)
  obtain ⟨g, ⟨hg⟩⟩ := ProjectiveBasic.CochainComplex.IsKProjective.exists_lift_through_quasiIso
    (extendMap p e) (extendMap f e)
  obtain ⟨g', hg'⟩ := (e.extendFunctor C).map_surjective g
  refine ⟨g', ⟨Homotopy.ofExtend (e := e) ?_⟩⟩
  simpa only [extendMap_comp, show extendMap g' e = g from hg'] using hg

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.ProjectiveModelComparison
