import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair

/-! # Quotient Gluing Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.QuotientGluingIs.Construction.QuotientGluing

/-!
# Gluing local quotient diagrams

Cartesian, surjective quotient maps transmit the local intersection condition
from a source cover to its quotient charts. This is the condition required by
the existing scheme-colimit gluing construction.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v w

/-- A cartesian natural transformation with surjective components sends a
locally directed source diagram to a locally directed quotient diagram. -/
theorem isLocallyDirected_of_equifibered_of_surjective
    {J : Type w} [Category.{v} J] {F G : J ⥤ Scheme.{u}}
    (q : F ⟶ G) (hq : q.Equifibered) (hqs : ∀ i, Surjective (q.app i))
    [(F ⋙ Scheme.forget).IsLocallyDirected] :
    (G ⋙ Scheme.forget).IsLocallyDirected := by
  constructor
  intro i j k fi fj yi yj heq
  change G.map fi yi = G.map fj yj at heq
  obtain ⟨xk, hxk⟩ := (hqs k).surj (G.map fi yi)
  obtain ⟨xi, hxi, hqi⟩ := Scheme.exists_preimage_of_isPullback (hq fi) xk yi hxk
  obtain ⟨xj, hxj, hqj⟩ := Scheme.exists_preimage_of_isPullback (hq fj) xk yj
    (hxk.trans heq)
  obtain ⟨l, fli, flj, x, hli, hlj⟩ :=
    (F ⋙ Scheme.forget).exists_map_eq_of_isLocallyDirected fi fj xi xj (hxi.trans hxj.symm)
  refine ⟨l, fli, flj, q.app l x, ?_, ?_⟩
  · change G.map fli (q.app l x) = yi
    change F.map fli x = xi at hli
    rw [← Scheme.Hom.comp_apply, ← q.naturality, Scheme.Hom.comp_apply, hli, hqi]
  · change G.map flj (q.app l x) = yj
    change F.map flj x = xj at hlj
    rw [← Scheme.Hom.comp_apply, ← q.naturality, Scheme.Hom.comp_apply, hlj, hqj]

/-- A property local on the target can be checked on any cartesian charts
above an open cover, rather than only the chosen categorical pullbacks. -/
theorem property_of_cartesian_openCover
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Y.OpenCover)
    {Xᵢ : 𝒰.I₀ → Scheme.{u}} (iX : ∀ i, Xᵢ i ⟶ X) (fᵢ : ∀ i, Xᵢ i ⟶ 𝒰.X i)
    (h : ∀ i, IsPullback (fᵢ i) (iX i) (𝒰.f i) f) (hf : ∀ i, P (fᵢ i)) : P f := by
  apply IsZariskiLocalAtTarget.of_openCover 𝒰
  intro i
  change P (pullback.snd f (𝒰.f i))
  rw [← (h i).flip.isoPullback_inv_snd, P.cancel_left_of_respectsIso]
  exact hf i

/-- Exact kernel pairs can be checked on cartesian quotient charts. The
relation chart is only required to be the source restriction of the original
relation; no global effectiveness assumption is made. -/
theorem isKernelPair_of_cartesian_openCover
    {R X Q : Scheme.{u}} (s t : R ⟶ X) (q : X ⟶ Q) (𝒰 : X.OpenCover)
    (Qᵢ Rᵢ : 𝒰.I₀ → Scheme.{u}) (qᵢ : ∀ i, 𝒰.X i ⟶ Qᵢ i)
    (jQ : ∀ i, Qᵢ i ⟶ Q) (jR : ∀ i, Rᵢ i ⟶ R)
    (sᵢ tᵢ : ∀ i, Rᵢ i ⟶ 𝒰.X i)
    (hs : ∀ i, IsPullback (sᵢ i) (jR i) (𝒰.f i) s)
    (ht : ∀ i, tᵢ i ≫ 𝒰.f i = jR i ≫ t)
    (hq : ∀ i, IsPullback (qᵢ i) (𝒰.f i) (jQ i) q)
    (hk : ∀ i, IsKernelPair (qᵢ i) (sᵢ i) (tᵢ i)) : IsKernelPair q s t := by
  apply Scheme.isPullback_of_openCover s t q q 𝒰
  intro i
  have h := (hk i).paste_vert (hq i)
  rw [(hq i).w, ht i] at h
  exact h.of_iso (hs i).flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by change sᵢ i ≫ 𝟙 _ = (hs i).flip.isoPullback.hom ≫ pullback.snd s (𝒰.f i)
        simpa only [Category.comp_id] using (hs i).flip.isoPullback_hom_snd.symm)
    (by change (jR i ≫ t) ≫ 𝟙 _ = (hs i).flip.isoPullback.hom ≫
          pullback.fst s (𝒰.f i) ≫ t
        simp) (by simp) (by simp)

variable {J : Type w} [Category.{v} J] [Small.{u} J] [Quiver.IsThin J]
variable (G : J ⥤ Scheme.{u})
variable [hG : ∀ {i j} (f : i ⟶ j), IsOpenImmersion (G.map f)]
variable [(G ⋙ Scheme.forget).IsLocallyDirected]

/-- A transparently indexed cover by the colimit charts. -/
noncomputable abbrev chartCover : (colimit G).OpenCover where
  I₀ := J
  X := G.obj
  f := colimit.ι G
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨Scheme.IsLocallyDirected.ι_jointly_surjective G, fun _ => inferInstance⟩

/-- The charts of a glued locally directed scheme retain their original
index category and transition maps as a locally directed open cover. -/
noncomputable local instance openCoverLocallyDirected :
    (chartCover G).LocallyDirected where
  trans := G.map
  trans_id := G.map_id
  trans_comp := G.map_comp
  w f := colimit.w G f
  property_trans {i j} f := by
    change IsOpenImmersion (G.map (show (i : J) ⟶ (j : J) from f))
    exact hG f
  directed {i j} x := by
    have heq : colimit.ι G i (pullback.fst (colimit.ι G i) (colimit.ι G j) x) =
        colimit.ι G j (pullback.snd (colimit.ι G i) (colimit.ι G j) x) := by
      exact congrArg (fun f => f x) (pullback.condition (f := colimit.ι G i) (g := colimit.ι G j))
    obtain ⟨k, fki, fkj, y, hyi, _⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff G).mp heq
    refine ⟨k, fki, fkj, y, ?_⟩
    have : IsOpenImmersion (colimit.ι G (show J from j)) := inferInstance
    apply (pullback.fst (colimit.ι G i) (colimit.ι G j)).isOpenEmbedding.injective
    change (pullback.lift (G.map fki) (G.map fkj) _ ≫
      pullback.fst (colimit.ι G i) (colimit.ι G j)) y = _
    rw [pullback.lift_fst]
    exact hyi

/-- An equifibered natural transformation provides relative gluing data over
the scheme obtained by gluing its target charts. -/
noncomputable def relativeData {F : J ⥤ Scheme.{u}} (q : F ⟶ G) (hq : q.Equifibered) :
    Scheme.Cover.RelativeGluingData (chartCover G) where
  functor := F
  natTrans := q
  equifibered := hq

/-- Finite locally free surjective chart maps glue to a finite locally free
surjective morphism, and the chart squares are cartesian. -/
theorem glued_projection_properties {F : J ⥤ Scheme.{u}} (q : F ⟶ G) (hq : q.Equifibered)
    (hf : ∀ i, IsFinite (q.app i)) (hflat : ∀ i, Flat (q.app i))
    (hfp : ∀ i, LocallyOfFinitePresentation (q.app i)) (hs : ∀ i, Surjective (q.app i)) :
    IsFinite (relativeData G q hq).toBase ∧ Flat (relativeData G q hq).toBase ∧
      LocallyOfFinitePresentation (relativeData G q hq).toBase ∧
      Surjective (relativeData G q hq).toBase := by
  let d := relativeData G q hq
  let : ∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f) := fun f =>
    MorphismProperty.of_isPullback (hq f).flip (hG f)
  let : (F ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.isLocallyDirected_of_equifibered_of_injective q hq fun f => (F.map f).injective
  let : HasColimit d.functor := inferInstanceAs (HasColimit F)
  let : IsZariskiLocalAtTarget (@IsFinite.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      IsFinite.instHasAffinePropertyAndIsAffineFiniteCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop
  let : IsZariskiLocalAtTarget (@Flat.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtTarget _ _ Flat.instHasRingHomPropertyFlat
  let : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtTarget _ _
      instHasRingHomPropertyLocallyOfFinitePresentationFinitePresentation
  have H (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
      (hp : ∀ i, P (q.app i)) : P d.toBase :=
    property_of_cartesian_openCover P d.toBase (chartCover G)
      (colimit.ι d.functor) d.natTrans.app d.isPullback_natTrans_ι_toBase hp
  exact ⟨H (fun {_ _} f => IsFinite f) hf, H (fun {_ _} f => Flat f) hflat,
    H (fun {_ _} f => LocallyOfFinitePresentation f) hfp, H @Surjective hs⟩

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.QuotientGluingIs.Construction.QuotientGluing
