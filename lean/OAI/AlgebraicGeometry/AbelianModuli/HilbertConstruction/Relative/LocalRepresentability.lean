import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.LocalRepresentationInjectivity
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Local Representability -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.LocalRepresentability

noncomputable section

/-! A relative Zariski sheaf with a jointly locally surjective family of representable open charts is represented by their constructed scheme gluing over the fixed base. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
variable {ι : Type u} {X : ι → Over S} {f : ∀ i, yoneda.obj (X i) ⟶ F}
variable (hf : ∀ i, (RepresentableOpenGlueData.relativeOpenImmersions S).presheaf (f i))
variable (hF : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F)
variable [Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S) (Sigma.desc f)]

theorem relativeLocalRepresentationMap_isIso : IsIso (LocalRepresentationSection.relativeLocalRepresentationMap hf hF) := by
  let J := Scheme.zariskiTopology.over S
  let M := LocalRepresentationSection.relativeLocalRepresentationScheme hf
  let α := LocalRepresentationSection.relativeLocalRepresentationMap hf hF
  have hfac : Sigma.desc (fun i => yoneda.map (LocalRepresentationSection.relativeLocalRepresentationInclusion hf i)) ≫ α =
      Sigma.desc f := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    exact LocalRepresentationSection.relativeLocalRepresentationMap_chart hf hF i
  have hsurj : Presheaf.IsLocallySurjective J α :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac
  have hinj : Presheaf.IsLocallyInjective J α :=
    Presheaf.isLocallyInjective_of_injective J α
      (fun T => LocalRepresentationInjectivity.relativeLocalRepresentationMap_injective hf hF T.unop)
  let β : J.yoneda.obj M ⟶ (⟨F, hF⟩ : Sheaf J (Type u)) := ⟨α⟩
  have : IsIso β := (Sheaf.isLocallyBijective_iff_isIso β).mp ⟨hinj, hsurj⟩
  exact inferInstanceAs (IsIso ((sheafToPresheaf J (Type u)).map β))

def relativeLocalRepresentationIso : F ≅ yoneda.obj (LocalRepresentationSection.relativeLocalRepresentationScheme hf) := by
  have : IsIso (LocalRepresentationSection.relativeLocalRepresentationMap hf hF) := relativeLocalRepresentationMap_isIso hf hF
  exact (asIso (LocalRepresentationSection.relativeLocalRepresentationMap hf hF)).symm

include hf hF in
theorem relativeLocallyRepresentable_isRepresentable : F.IsRepresentable := by
  exact ⟨LocalRepresentationSection.relativeLocalRepresentationScheme hf,
    ⟨Functor.representableByEquiv.symm (relativeLocalRepresentationIso hf hF).symm⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.LocalRepresentability
