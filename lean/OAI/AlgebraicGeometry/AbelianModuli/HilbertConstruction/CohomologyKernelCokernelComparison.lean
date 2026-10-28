import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.ExactFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.Additivity

/-! # Cohomology Kernel Cokernel Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyKernelCokernelComparison

noncomputable section

/-! A morphism preserves finiteness of all genuine cohomology when its actual kernel and cokernel have finite cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u v

private theorem property_iff_of_kernel_cokernel
    {C : Type u} [Category.{v} C] [Abelian C] (P : C → Prop)
    (hmid : ∀ {S : ShortComplex C}, S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    (hleft : ∀ {S : ShortComplex C}, S.ShortExact → P S.X₂ → P S.X₃ → P S.X₁)
    (hright : ∀ {S : ShortComplex C}, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
    (hiso : ∀ {A B : C}, (A ≅ B) → P A → P B)
    {M N : C} (a : M ⟶ N) (hK : P (kernel a)) (hC : P (cokernel a)) :
    P M ↔ P N := by
  let S₁ : ShortComplex C := ShortComplex.mk (kernel.ι a) (Abelian.coimage.π a) (by simp)
  let S₂ : ShortComplex C := ShortComplex.mk (Abelian.image.ι a) (cokernel.π a) (by simp)
  have hS₁ : S₁.ShortExact := ⟨ShortComplex.cokernelSequence_exact (kernel.ι a)⟩
  have hS₂ : S₂.ShortExact := ⟨ShortComplex.kernelSequence_exact (cokernel.π a)⟩
  constructor
  · intro hM
    have hI : P (Abelian.coimage a) := hright hS₁ hK hM
    exact hmid hS₂ (hiso (Abelian.coimageIsoImage a) hI) hC
  · intro hN
    have hI : P (Abelian.image a) := hleft hS₂ hN hC
    exact hmid hS₁ hK (hiso (Abelian.coimageIsoImage a).symm hI)

namespace ZariskiCohomology.CoefficientCohomologyFinite

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite.iff_of_kernel_cokernel {X : Scheme.{u}} {R : Type u} [CommRing R] [IsNoetherianRing R]
    (c : R →+* Γ(X, ⊤)) {M N : X.Modules} (a : M ⟶ N)
    (hK : CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c (kernel a))
    (hC : CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c (cokernel a)) :
    CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c M ↔ CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c N :=
  property_iff_of_kernel_cokernel (CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c)
    (fun h h₁ h₃ => CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite.middle c h h₁ h₃) (fun h h₂ h₃ => CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite.left c h h₂ h₃)
    (fun h h₁ h₂ => CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite.right c h h₁ h₂) (fun e h => CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite.of_iso c e h) a hK hC

end ZariskiCohomology.CoefficientCohomologyFinite

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyKernelCokernelComparison
