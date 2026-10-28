import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

/-! # Coproduct Section Surjection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.CoproductSectionSurjection

noncomputable section

/-! A coproduct of module maps is surjective on sections when its summand images contain a spanning family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

theorem module_coproduct_desc_section_surjective {X : Scheme.{u}} {ι : Type u} {κ : Type v}
    (F : ι → X.Modules) {M : X.Modules} (φ : ∀ i, F i ⟶ M) (U : X.Opens)
    (s : κ → Γ(M, U)) (hs : Submodule.span Γ(X, U) (Set.range s) = ⊤)
    (hlift : ∀ k, ∃ (i : ι) (t : Γ(F i, U)), (φ i).app U t = s k) :
    Function.Surjective ((Sigma.desc φ).app U) := by
  let a := Tensor.Powers.SheafMultilinearMap.homApp (Sigma.desc φ) U
  change Function.Surjective a
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hs]
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  obtain ⟨i, t, ht⟩ := hlift k
  refine ⟨(Sigma.ι F i).app U t, ?_⟩
  exact (ConcreteCategory.congr_hom
    (congrArg (fun f : F i ⟶ M => f.app U) (Sigma.ι_comp_desc φ i)) t).trans ht

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.CoproductSectionSurjection
