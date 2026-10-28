import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AmpleFiniteSectionNeighborhood
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AmpleNorm
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Ample Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AmpleDescent.Construction

noncomputable section

/-! Ampleness descends through an actual finite-flat quotient over an
infinite field. The proof constructs source sections avoiding each
whole fibre and takes their global norms; it assumes no section-
avoidance or compatibility datum. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem quotient_isAmple_of_pullback
    {K : Type u} [Field K] [Infinite K]
    {H S R X Y : Scheme.{u}} [IsAffine H] [IsAffine S]
    (q : X ⟶ Y) [IsFinite q] [Flat q] [Surjective q] [LocallyOfFinitePresentation q]
    (s t : R ⟶ X) (hk : IsKernelPair q s t)
    (h : H ⟶ S) [IsFinite h] (a : X ⟶ S) (r : R ⟶ H)
    (hs : IsPullback r s h a) {ι : Type v} [Fintype ι]
    (b : letI := h.appTop.hom.toAlgebra; Module.Basis ι Γ(S, ⊤) Γ(H, ⊤))
    (f : X ⟶ Spec (.of K)) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (d : ℕ) (hdegree : ∀ y : Y, q.finrank y = d)
    (hL : (L.pullback q).IsAmple) : L.IsAmple := by
  apply AmpleNorm.Construction.quotient_isAmple_of_fiber_sections q s t hk h a r hs b L d hdegree hL.1
  intro y
  obtain ⟨n, hn, z, hz, hza⟩ := AmpleFiniteSectionNeighborhood.Construction.ample_finite_section_neighborhood f (L.pullback q) hL
    (q ⁻¹' {y}) (q.finite_preimage_singleton y)
  let z' := z ≫ (L.powerBaseChangeIso q n).inv
  have hD : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z' = AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z :=
    AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso z (L.powerBaseChangeIso q n).symm
  refine ⟨n, hn, z', ?_, (congrArg IsAffineOpen hD).mpr hza⟩
  intro x hx
  exact (congrArg (fun U : X.Opens => x ∈ U) hD).mpr (hz x hx)

theorem quotient_isAmple_of_pullback_connected
    {K : Type u} [Field K] [Infinite K]
    {H S R X Y : Scheme.{u}} [IsAffine H] [IsAffine S] [PreconnectedSpace Y]
    (q : X ⟶ Y) [IsFinite q] [Flat q] [Surjective q] [LocallyOfFinitePresentation q]
    (s t : R ⟶ X) (hk : IsKernelPair q s t)
    (h : H ⟶ S) [IsFinite h] (a : X ⟶ S) (r : R ⟶ H)
    (hs : IsPullback r s h a) {ι : Type v} [Fintype ι]
    (b : letI := h.appTop.hom.toAlgebra; Module.Basis ι Γ(S, ⊤) Γ(H, ⊤))
    (f : X ⟶ Spec (.of K)) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (y₀ : Y)
    (hL : (L.pullback q).IsAmple) : L.IsAmple := by
  apply quotient_isAmple_of_pullback q s t hk h a r hs b f L (q.finrank y₀) _ hL
  intro y
  exact q.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace y y₀

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AmpleDescent.Construction
