import OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizedComplex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizationInjectivityEq

/-! # Localized Left -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizedLeft.LocalizedLeftExactness

noncomputable section

/-!
# Left exactness detected on principal localizations

Both exactness and injectivity of a short complex descend along a
unit-ideal family of principal module localizations.
-/

open _root_.CategoryTheory

universe u

variable (R ι : Type u) [CommRing R] (s : ι → R) (hs : Ideal.span (Set.range s) = ⊤)

include hs in
theorem leftExact (C : ShortComplex (ModuleCat.{u} R)) (CL : ι → ShortComplex (ModuleCat.{u} R))
    (φ : ∀ i, C ⟶ CL i)
    [∀ i, IsLocalizedModule (Submonoid.powers (s i)) ((φ i).τ₁).hom]
    [∀ i, IsLocalizedModule (Submonoid.powers (s i)) ((φ i).τ₂).hom]
    (hCL : ∀ i, (CL i).Exact ∧ Mono (CL i).f) : C.Exact ∧ Mono C.f := by
  refine ⟨LocalizedComplex.LocalizedComplexExactness.shortComplex R ι s hs C CL φ (fun i => (hCL i).1), ?_⟩
  apply (ModuleCat.mono_iff_injective C.f).mpr
  exact LocalizationInjectivityEq.LocalizationInjectivity.injective R ι C.X₁ s (fun i => (CL i).X₁)
    (fun i => ((φ i).τ₁).hom) C.X₂ C.f.hom (fun i => (CL i).X₂)
    (fun i => ((φ i).τ₂).hom) (fun i => (CL i).f.hom)
    (fun i x => (congrArg (fun h : C.X₁ ⟶ (CL i).X₂ => h.hom x) (φ i).comm₁₂).symm)
    hs (fun i => (ModuleCat.mono_iff_injective (CL i).f).mp (hCL i).2)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizedLeft.LocalizedLeftExactness
