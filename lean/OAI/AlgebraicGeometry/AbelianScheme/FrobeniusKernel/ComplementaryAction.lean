import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ComplementaryIsogeny
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData

/-! # Complementary Action -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ComplementaryAction.Construction

noncomputable section

/-! The actual complementary isogeny is coefficient-linear and has
the same scalar kernel bound, by its two scalar-composition equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {g h : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (d : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (m : ℕ)
  {O : Type u} [CommRing O]
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O B)

theorem complementaryIsogeny_action
    (hc : ∀ a, ρ.map a ≫ f.hom = f.hom ≫ σ.map a)
    (hfd : f.hom ≫ d.hom = (𝟙 A.scheme) ^ m) (a : O) :
    σ.map a ≫ d.hom = d.hom ≫ ρ.map a := by
  have : EffectiveEpi f.hom := PELModuli.IntegralModel.IsogenyFactorizationIs.IsogenyFactorization.effectiveEpi_over_of_fpqc f.hom
  apply (cancel_epi f.hom).mp
  rw [← Category.assoc, ← hc a, Category.assoc, hfd, ← Category.assoc, hfd,
    MonObj.comp_pow, MonObj.pow_comp, Category.comp_id, Category.id_comp]

omit [CommRing O] in
theorem complementaryIsogeny_kernel_killed
    (hdf : d.hom ≫ f.hom = (𝟙 B.scheme) ^ m)
    (T : Over S) (x : T ⟶ B.scheme) (hx : x ≫ d.hom = 1) : x ^ m = 1 := by
  have h := congrArg (fun z => x ≫ z) hdf
  rw [← Category.assoc, hx, MonObj.one_comp, MonObj.comp_pow, Category.comp_id] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ComplementaryAction.Construction
