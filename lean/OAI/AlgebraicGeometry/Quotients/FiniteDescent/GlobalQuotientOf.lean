import OAI.AlgebraicGeometry.Quotients.FiniteDescent.QuotientGluingIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Quotient
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Global Quotient Of -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.GlobalQuotientOf.Construction.GlobalQuotient

/-!
# Global quotients from compatible local quotient charts

The source is the original scheme, identified with the gluing of its open
cover. The hypotheses concern only local quotient maps and their cartesian
transition squares. Effectiveness and the universal property of the global
map are conclusions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

attribute [local instance] QuotientGluingIs.Construction.QuotientGluing.openCoverLocallyDirected

/-- Compatible finite locally free quotient charts produce a quotient of the
original scheme, with the prescribed global kernel pair and descent for every
scheme target. -/
theorem exists_of_cartesian_charts
    {R X : Scheme.{u}} (s t : R ⟶ X) (𝒰 : X.OpenCover)
    [Category.{v} 𝒰.I₀] [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] [𝒰.LocallyDirected]
    (G : 𝒰.I₀ ⥤ Scheme.{u})
    [hG : ∀ {i j} (f : i ⟶ j), IsOpenImmersion (G.map f)]
    (q : 𝒰.functorOfLocallyDirected ⟶ G) (hq : q.Equifibered)
    (hf : ∀ i, IsFinite (q.app i)) (hflat : ∀ i, Flat (q.app i))
    (hfp : ∀ i, LocallyOfFinitePresentation (q.app i)) (hsurj : ∀ i, Surjective (q.app i))
    (Rᵢ : 𝒰.I₀ → Scheme.{u}) (jR : ∀ i, Rᵢ i ⟶ R)
    (sᵢ tᵢ : ∀ i, Rᵢ i ⟶ 𝒰.X i)
    (hs : ∀ i, IsPullback (sᵢ i) (jR i) (𝒰.f i) s)
    (ht : ∀ i, tᵢ i ≫ 𝒰.f i = jR i ≫ t)
    (hk : ∀ i, IsKernelPair (q.app i) (sᵢ i) (tᵢ i)) :
    ∃ (Q : Scheme.{u}) (π : X ⟶ Q),
      IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π ∧ Surjective π ∧
      IsKernelPair π s t ∧
      ∀ (T : Scheme.{u}) (f : X ⟶ T), s ≫ f = t ≫ f →
        ∃! g : Q ⟶ T, π ≫ g = f := by
  let : (G ⋙ Scheme.forget).IsLocallyDirected :=
    QuotientGluingIs.Construction.QuotientGluing.isLocallyDirected_of_equifibered_of_surjective q hq hsurj
  let F := 𝒰.functorOfLocallyDirected
  let d := QuotientGluingIs.Construction.QuotientGluing.relativeData G q hq
  let e : colimit F ≅ X :=
    (colimit.isColimit F).coconePointUniqueUpToIso 𝒰.isColimitCoconeOfLocallyDirected
  let q₀ : colimit F ⟶ colimit G := d.toBase
  let π : X ⟶ colimit G := e.inv ≫ q₀
  have he (i : 𝒰.I₀) : colimit.ι F i ≫ e.hom = 𝒰.f i := by
    exact (colimit.isColimit F).comp_coconePointUniqueUpToIso_hom
      𝒰.isColimitCoconeOfLocallyDirected i
  have hcharts (i : 𝒰.I₀) : IsPullback (q.app i) (𝒰.f i) (colimit.ι G i) π := by
    have h : IsPullback (q.app i) (colimit.ι F i) (colimit.ι G i) q₀ :=
      d.isPullback_natTrans_ι_toBase i
    exact h.of_iso
      (Iso.refl _) (Iso.refl _) e (Iso.refl _)
      (by simp) (by exact (he i).trans (Category.id_comp _).symm) (by simp)
      (by change q₀ ≫ 𝟙 _ = e.hom ≫ e.inv ≫ q₀
          exact (Category.comp_id _).trans (e.hom_inv_id_assoc _).symm)
  obtain ⟨hfin, hfl, hpres, hsur⟩ := QuotientGluingIs.Construction.QuotientGluing.glued_projection_properties G q hq
    hf hflat hfp hsurj
  let : IsFinite q₀ := hfin
  let : Flat q₀ := hfl
  let : LocallyOfFinitePresentation q₀ := hpres
  let : Surjective q₀ := hsur
  have hπfin : IsFinite π := by dsimp [π]; infer_instance
  have hπflat : Flat π := by dsimp [π]; infer_instance
  have hπfp : LocallyOfFinitePresentation π := by dsimp [π]; infer_instance
  have hπsurj : Surjective π := by dsimp [π]; infer_instance
  have hπker : IsKernelPair π s t := QuotientGluingIs.Construction.QuotientGluing.isKernelPair_of_cartesian_openCover
    s t π 𝒰 G.obj Rᵢ q.app (colimit.ι G) jR sᵢ tᵢ hs ht hcharts hk
  refine ⟨colimit G, π, hπfin, hπflat, hπfp, hπsurj, hπker, ?_⟩
  intro T f h
  exact Quotient.Construction.QuotientDescent.existsUnique_desc π hπker f h

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.GlobalQuotientOf.Construction.GlobalQuotient
