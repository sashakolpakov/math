import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.AlbaneseGeneration
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ProductGeometry
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricExt
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition

/-! # Albanese Ext -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.AlbaneseExt

noncomputable section

/-! Generation detects actual integral endomorphisms of the complete
product Albanese. Smoothness and properness justify geometric extensionality. -/

set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

namespace Construction
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricExt

theorem over_iso_smooth_proper {S : Scheme.{0}} {X Y : Over S} (e : X ≅ Y)
    (hY : Smooth Y.hom ∧ IsProper Y.hom) : Smooth X.hom ∧ IsProper X.hom := by
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  have : Smooth Y.hom := hY.1
  have : IsProper Y.hom := hY.2
  rw [← e.hom.w]
  exact ⟨inferInstance, inferInstance⟩

theorem finite_product_smooth_proper {S : Scheme.{0}} (n : ℕ) (X : Fin n → Over S)
    (hX : ∀ j, Smooth (X j).hom ∧ IsProper (X j).hom) :
    Smooth (∏ᶜ X).hom ∧ IsProper (∏ᶜ X).hom := by
  induction n with
  | zero =>
    apply over_iso_smooth_proper (PELModuli.IntegralModel.ProductGeometry.piZeroIso X)
    exact ⟨inferInstanceAs (Smooth (𝟙 S)), inferInstanceAs (IsProper (𝟙 S))⟩
  | succ n ih =>
    obtain ⟨hs, hp⟩ := ih (fun j : Fin n => X j.succ) (fun j => hX j.succ)
    have : Smooth (X 0).hom := (hX 0).1
    have : IsProper (X 0).hom := (hX 0).2
    apply over_iso_smooth_proper (PELModuli.IntegralModel.ProductGeometry.piSuccIso X)
    change Smooth (pullback.fst (X 0).hom (∏ᶜ fun j : Fin n => X j.succ).hom ≫ (X 0).hom) ∧
      IsProper (pullback.fst (X 0).hom (∏ᶜ fun j : Fin n => X j.succ).hom ≫ (X 0).hom)
    exact ⟨inferInstance, inferInstance⟩

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]

theorem albaneseGroup_smooth_proper
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry) :
    Smooth D.albaneseGroup.X.hom ∧ IsProper D.albaneseGroup.X.hom := by
  have hp := finite_product_smooth_proper D.componentCount (fun j => (D.components.A j).X)
    (fun j => ⟨(hgeometry.abelianGeometry j).1, (hgeometry.abelianGeometry j).2.1⟩)
  obtain ⟨hs, ht⟩ := over_iso_smooth_proper (TateComparison.Products.componentProductComparison D.components.A) hp
  exact ⟨inferInstanceAs (Smooth (pullback.snd (TateComparison.Products.componentProduct D.components.A).X.hom D.generic)),
    inferInstanceAs (IsProper (pullback.snd (TateComparison.Products.componentProduct D.components.A).X.hom D.generic))⟩

theorem endPoint_eq_app (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (a : D.EndK)
    (T : Over (Spec (.of K))) (z : Additive (T ⟶ D.albaneseGroup.X)) :
    D.endPoint a z = (a.app (.op T)).hom z := by
  apply Additive.toMul.injective
  exact (TateComparison.End.endSchemeMap_points D.albaneseGroup.X a T z.toMul).symm

theorem albanese_end_eq_one_of_differences
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry) (a : D.EndK)
    (ha : ∀ (k : Type) [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ Spec (.of K))
      (j : Fin D.componentCount) (x y : Over.mk b ⟶ D.componentGeneric j),
      D.endPoint a (D.aPoint hgeometry j x - D.aPoint hgeometry j y) =
        D.aPoint hgeometry j x - D.aPoint hgeometry j y) : a = 1 := by
  obtain ⟨hs, hp⟩ := albaneseGroup_smooth_proper D hgeometry
  have : IsReduced D.albaneseGroup.X.left := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced D.albaneseGroup.X.hom
  apply TateComparison.End.endSchemeMap_injective D.albaneseGroup.X
  rw [TateComparison.BaseChange.endSchemeMap_one]
  apply TateComparison.GeometricExt.over_hom_ext_geometric
  intro k _ _ b x
  have hfix : ∀ z, (a.app (.op (Over.mk b))).hom z = z := by
    apply AlbaneseGeneration.Construction.albanese_point_end_eq_of_differences D hgeometry b
    intro j y z
    exact (endPoint_eq_app D a (Over.mk b)
      (D.aPoint hgeometry j y - D.aPoint hgeometry j z)).symm.trans (ha k b j y z)
  have hx := congrArg Additive.toMul (hfix (Additive.ofMul x))
  rw [TateComparison.End.endSchemeMap_points] at hx
  exact hx.trans (Category.comp_id x).symm

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.AlbaneseExt
