import OAI.AlgebraicGeometry.Picard.PoincareBundle.EffectiveQuotientFactor
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.PreimageQuotient

/-! # Decomposition Quotient -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.DecompositionQuotient

noncomputable section

/-! A scheme-valued kernel decomposition identifies the descended kernel through its actual finite flat quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

attribute [local instance] Kernel.Scheme.kernelGroup

variable {S : Scheme.{u}} {A B D Z : Over S} [GrpObj A] [GrpObj B] [GrpObj D] [GrpObj Z]
  (f : A ⟶ B) [IsMonHom f] (m : B ⟶ D) [IsMonHom m] (φ : A ⟶ Z) [IsMonHom φ]
  [IsFinite f.left] [Flat f.left] [Surjective f.left]
  (j : Kernel.Scheme.kernelObject φ ⟶ Kernel.Scheme.kernelObject m) [Mono j]
  (hj : j ≫ Kernel.Scheme.kernelInclusion m = Kernel.Scheme.kernelInclusion φ ≫ f)
  (hd : ∀ (T : Over S) (x : T ⟶ Kernel.Scheme.kernelObject (f ≫ m)),
    ∃ a : T ⟶ Kernel.Scheme.kernelObject f, ∃ b : T ⟶ Kernel.Scheme.kernelObject φ,
      x ≫ Kernel.Scheme.kernelInclusion (f ≫ m) = (a ≫ Kernel.Scheme.kernelInclusion f) * (b ≫ Kernel.Scheme.kernelInclusion φ))

include hj hd

omit [IsMonHom φ] [IsFinite f.left] [Flat f.left] [Surjective f.left] [Mono j] in
/-- The full scheme-valued decomposition factors the restricted quotient through the original kernel embedding. -/
theorem exists_factor : ∃ r : Kernel.Scheme.kernelObject (f ≫ m) ⟶ Kernel.Scheme.kernelObject φ,
    r ≫ j = PreimageQuotient.map f m := by
  obtain ⟨a, b, hab⟩ := hd (Kernel.Scheme.kernelObject (f ≫ m)) (𝟙 (Kernel.Scheme.kernelObject (f ≫ m)))
  refine ⟨b, ?_⟩
  apply (cancel_mono (Kernel.Scheme.kernelInclusion m)).mp
  rw [Category.assoc, hj, PreimageQuotient.map_inclusion]
  have h := congrArg (fun z => z ≫ f) hab
  simp only [Category.id_comp, MonObj.mul_comp, Category.assoc, Kernel.Scheme.kernelInclusion_comp,
    MonObj.comp_one, one_mul] at h
  exact h.symm

/-- The finite flat restricted quotient and the original-kernel embedding construct an actual kernel isomorphism. -/
def kernelIso : Kernel.Scheme.kernelObject φ ≅ Kernel.Scheme.kernelObject m := by
  let r := Classical.choose (exists_factor f m φ j hj hd)
  have hr : r ≫ j = PreimageQuotient.map f m := Classical.choose_spec (exists_factor f m φ j hj hd)
  have : EffectiveEpi (PreimageQuotient.map f m) := PreimageQuotient.effectiveEpi f m
  exact EffectiveQuotientFactor.factorIso (PreimageQuotient.map f m) j r hr

omit [IsMonHom φ] in
/-- Its forward morphism is exactly the given original-kernel embedding. -/
theorem kernelIso_hom : (kernelIso f m φ j hj hd).hom = j := by
  unfold kernelIso
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.DecompositionQuotient
