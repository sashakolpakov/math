import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

/-! # Split Extension -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitExtension.Lifts

noncomputable section

/-!
A section of the component quotient constructs the product decomposition
with its scheme-theoretic kernel. The proof works on every test scheme,
so the connected factor retains its infinitesimal sections.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {S : Scheme.{u}} {A E : Over S} [GrpObj A] [GrpObj E] [IsCommMonObj A]
variable (π : A ⟶ E) [IsMonHom π] (σ : E ⟶ A) [IsMonHom σ]

def splitExtensionMap : Picard.PoincareBundle.Kernel.Scheme.kernelObject π ⊗ E ⟶ A :=
  (fst (Picard.PoincareBundle.Kernel.Scheme.kernelObject π) E ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π) * (snd (Picard.PoincareBundle.Kernel.Scheme.kernelObject π) E ≫ σ)

instance splitExtensionMap_isMonHom : IsMonHom (splitExtensionMap π σ) := by
  change IsMonHom (lift (fst (Picard.PoincareBundle.Kernel.Scheme.kernelObject π) E ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π)
    (snd (Picard.PoincareBundle.Kernel.Scheme.kernelObject π) E ≫ σ) ≫ μ[A])
  infer_instance

omit [IsCommMonObj A] [IsMonHom σ] in
theorem splitExtensionMap_projection (hσ : σ ≫ π = 𝟙 E) :
    splitExtensionMap π σ ≫ π = snd (Picard.PoincareBundle.Kernel.Scheme.kernelObject π) E := by
  rw [splitExtensionMap, MonObj.mul_comp, Category.assoc, Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp,
    MonObj.comp_one, Category.assoc, hσ, Category.comp_id, one_mul]

omit [IsCommMonObj A] [IsMonHom σ] in
theorem splitExtensionMap_points_bijective (hσ : σ ≫ π = 𝟙 E) (T : Over S) :
    Function.Bijective (fun x : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject π ⊗ E => x ≫ splitExtensionMap π σ) := by
  constructor
  · intro x y h
    have he : x ≫ snd (Picard.PoincareBundle.Kernel.Scheme.kernelObject π) E = y ≫ snd (Picard.PoincareBundle.Kernel.Scheme.kernelObject π) E := by
      have hz := congrArg (fun a => a ≫ π) h
      simpa only [Category.assoc, splitExtensionMap_projection π σ hσ] using hz
    have hk : (x ≫ fst (Picard.PoincareBundle.Kernel.Scheme.kernelObject π) E) ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π =
        (y ≫ fst (Picard.PoincareBundle.Kernel.Scheme.kernelObject π) E) ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π := by
      have hz : ((x ≫ fst (Picard.PoincareBundle.Kernel.Scheme.kernelObject π) E) ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π) *
          ((x ≫ snd (Picard.PoincareBundle.Kernel.Scheme.kernelObject π) E) ≫ σ) =
        ((y ≫ fst (Picard.PoincareBundle.Kernel.Scheme.kernelObject π) E) ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π) *
          ((y ≫ snd (Picard.PoincareBundle.Kernel.Scheme.kernelObject π) E) ≫ σ) := by
        simpa only [splitExtensionMap, MonObj.comp_mul, Category.assoc] using h
      rw [he] at hz
      exact mul_right_cancel hz
    apply CartesianMonoidalCategory.hom_ext
    · exact (cancel_mono (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π)).mp hk
    · exact he
  · intro x
    let d : T ⟶ A := x * ((x ≫ π) ≫ σ)⁻¹
    have hd : d ≫ π = 1 := by
      rw [show d = x * ((x ≫ π) ≫ σ)⁻¹ from rfl,
        MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hσ,
        Category.comp_id, mul_inv_cancel]
    let k := (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv π T).symm ⟨d, hd⟩
    have hk : k ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π = d :=
      congrArg Subtype.val ((Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv π T).apply_symm_apply ⟨d, hd⟩)
    refine ⟨lift k (x ≫ π), ?_⟩
    change lift k (x ≫ π) ≫ splitExtensionMap π σ = x
    rw [splitExtensionMap, MonObj.comp_mul, ← Category.assoc, lift_fst,
      ← Category.assoc, lift_snd, hk]
    exact inv_mul_cancel_right x ((x ≫ π) ≫ σ)

/-- The product splitting is a constructed scheme isomorphism. -/
def splitExtensionIso (hσ : σ ≫ π = 𝟙 E) : Picard.PoincareBundle.Kernel.Scheme.kernelObject π ⊗ E ≅ A := by
  have : IsIso (splitExtensionMap π σ) :=
    isIso_of_yoneda_map_bijective _ (splitExtensionMap_points_bijective π σ hσ)
  exact asIso (splitExtensionMap π σ)

instance splitExtensionIso_isMonHom (hσ : σ ≫ π = 𝟙 E) :
    IsMonHom (splitExtensionIso π σ hσ).hom :=
  inferInstanceAs (IsMonHom (splitExtensionMap π σ))

omit [IsCommMonObj A] in
theorem splitExtensionIso_kernel_inclusion (hσ : σ ≫ π = 𝟙 E) :
    lift (𝟙 (Picard.PoincareBundle.Kernel.Scheme.kernelObject π)) (1 : Picard.PoincareBundle.Kernel.Scheme.kernelObject π ⟶ E) ≫
      (splitExtensionIso π σ hσ).hom = Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π := by
  change lift (𝟙 (Picard.PoincareBundle.Kernel.Scheme.kernelObject π)) 1 ≫ splitExtensionMap π σ = _
  rw [splitExtensionMap, MonObj.comp_mul, ← Category.assoc, lift_fst,
    Category.id_comp, ← Category.assoc, lift_snd, MonObj.one_comp, mul_one]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitExtension.Lifts
