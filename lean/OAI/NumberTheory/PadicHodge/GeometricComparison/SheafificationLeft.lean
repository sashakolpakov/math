import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Sheafification Left -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationLeft.SheafificationLeftExactness

noncomputable section

/-! Exactness after sheafification reflects to a short complex whose three presheaves already satisfy the sheaf condition. -/

open _root_.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasSheafify J D]
  (S : ShortComplex (Cᵒᵖ ⥤ D))
  (h₁ : Presheaf.IsSheaf J S.X₁) (h₂ : Presheaf.IsSheaf J S.X₂) (h₃ : Presheaf.IsSheaf J S.X₃)

def unitIso : S ≅ (S.map (presheafToSheaf J D)).map (sheafToPresheaf J D) :=
  ShortComplex.isoMk (isoSheafify J h₁) (isoSheafify J h₂) (isoSheafify J h₃)
    (toSheafify_naturality J S.f).symm (toSheafify_naturality J S.g).symm

include h₁ h₂ h₃ in
theorem of_sheafification (hE : (S.map (presheafToSheaf J D)).Exact)
    [Mono (S.map (presheafToSheaf J D)).f] : S.Exact ∧ Mono S.f := by
  have hmap := hE.map_of_mono_of_preservesKernel (sheafToPresheaf J D) inferInstance inferInstance
  apply (ShortComplex.exact_and_mono_f_iff_of_iso (unitIso J S h₁ h₂ h₃)).mpr
  refine ⟨hmap, ?_⟩
  change Mono ((sheafToPresheaf J D).map (S.map (presheafToSheaf J D)).f)
  infer_instance

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationLeft.SheafificationLeftExactness
