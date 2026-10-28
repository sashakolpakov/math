import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TraceAllTests
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ProductGeometry
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition

/-! # Albanese Trace -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The IntegralModel geometry supplies the hypotheses for the actual algebraic
trace from the moduli space to its product Albanese over the number field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem AlbaneseTrace.over_iso_separated {S : Scheme.{0}} {X Y : Over S}
    (e : X ≅ Y) [IsSeparated Y.hom] : IsSeparated X.hom := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  rw [← e.hom.w]
  infer_instance

theorem AlbaneseTrace.finite_product_separated {S : Scheme.{0}} (n : ℕ) (X : Fin n → Over S)
    [∀ i, IsSeparated (X i).hom] : IsSeparated (∏ᶜ X).hom := by
  induction n with
  | zero =>
    have : IsSeparated (𝟙_ (Over S)).hom := inferInstanceAs (IsSeparated (𝟙 S))
    exact AlbaneseTrace.over_iso_separated (PELModuli.IntegralModel.ProductGeometry.piZeroIso X)
  | succ n ih =>
    have : IsSeparated (∏ᶜ fun i : Fin n => X i.succ).hom := ih (fun i => X i.succ)
    have : IsSeparated (X 0 ⊗ ∏ᶜ fun i : Fin n => X i.succ).hom := by
      change IsSeparated (pullback.fst (X 0).hom (∏ᶜ fun i : Fin n => X i.succ).hom ≫ (X 0).hom)
      infer_instance
    exact AlbaneseTrace.over_iso_separated (PELModuli.IntegralModel.ProductGeometry.piSuccIso X)

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.HasIntegralModelGeometry)

include h

theorem Data.SphericalPELAlbaneseData.genericSpace_smooth : Smooth D.space.hom := by
  have : Smooth D.model.space.hom := h.smooth
  exact inferInstanceAs (Smooth (pullback.snd D.model.space.hom D.generic))

theorem Data.SphericalPELAlbaneseData.genericSpace_reduced : IsReduced D.space.left := by
  have := D.genericSpace_smooth h
  exact Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced D.space.hom

theorem Data.SphericalPELAlbaneseData.genericSpace_locallyNoetherian : IsLocallyNoetherian D.space.left := by
  have := D.genericSpace_smooth h
  exact LocallyOfFiniteType.isLocallyNoetherian D.space.hom

theorem Data.SphericalPELAlbaneseData.albaneseGroup_separated : IsSeparated D.albaneseGroup.X.hom := by
  have (j : Fin D.componentCount) : IsSeparated (D.components.A j).X.hom := by
    have : IsProper (D.components.A j).X.hom := (h.abelianGeometry j).2.1
    infer_instance
  have : IsSeparated (∏ᶜ fun j => (D.components.A j).X).hom :=
    AlbaneseTrace.finite_product_separated D.componentCount (fun j => (D.components.A j).X)
  have : IsSeparated (Products.componentProduct D.components.A).X.hom :=
    AlbaneseTrace.over_iso_separated (Products.componentProductComparison D.components.A)
  exact inferInstanceAs (IsSeparated (pullback.snd (Products.componentProduct D.components.A).X.hom D.generic))

/-- The actual finite-etale correspondence trace into the Albanese over K. -/
def Data.SphericalPELAlbaneseData.albaneseTrace (t : Local.IntegralType s) : D.space ⟶ D.albaneseGroup.X := by
  have : IsReduced D.space.left := D.genericSpace_reduced h
  have : IsLocallyNoetherian D.space.left := D.genericSpace_locallyNoetherian h
  have : IsSeparated D.albaneseGroup.X.hom := D.albaneseGroup_separated h
  exact (D.correspondence t).algebraicTrace (D.albaneseMap h)

theorem Data.SphericalPELAlbaneseData.albaneseTrace_geometric (t : Local.IntegralType s) {k : Type} [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ Spec (.of K)) (x : Over.mk b ⟶ D.space) :
    x ≫ D.albaneseTrace h t =
      (((D.correspondence t).neighbors b x).map (fun y => y ≫ D.albaneseMap h)).prod := by
  have : IsReduced D.space.left := D.genericSpace_reduced h
  have : IsLocallyNoetherian D.space.left := D.genericSpace_locallyNoetherian h
  have : IsSeparated D.albaneseGroup.X.hom := D.albaneseGroup_separated h
  exact (D.correspondence t).algebraicTrace_geometric (D.albaneseMap h) b x

theorem Data.SphericalPELAlbaneseData.albaneseTrace_local (t : Local.IntegralType s) {T : Over (Spec (.of K))}
    (x : T ⟶ D.space) {n : ℕ} (e : (D.correspondence t).BranchSplitting x n) :
    x ≫ D.albaneseTrace h t =
      ∏ i : Fin n, (D.correspondence t).endpoint ((D.correspondence t).splitBranch x e i) ≫ D.albaneseMap h := by
  have : IsReduced D.space.left := D.genericSpace_reduced h
  have : IsLocallyNoetherian D.space.left := D.genericSpace_locallyNoetherian h
  have : IsSeparated D.albaneseGroup.X.hom := D.albaneseGroup_separated h
  exact (D.correspondence t).algebraicTrace_local (D.albaneseMap h) x e

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
