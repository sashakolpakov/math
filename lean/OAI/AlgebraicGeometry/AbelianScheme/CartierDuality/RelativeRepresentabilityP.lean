import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeGluing
import Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-! # Relative Representability P -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeRepresentabilityP.Construction.Schemes

noncomputable section

/-!
# CartierDuality: representability is local over a fixed base
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

/-- Open immersions in the category of schemes over a fixed base. -/
abbrev relativeOpenImmersion (S : Scheme.{u}) : MorphismProperty (Over S) :=
  (@IsOpenImmersion).inverseImage (Over.forget S)

/-- A relative open immersion is a monomorphism of schemes over the base. -/
theorem relativeOpenImmersion_le_monomorphisms (S : Scheme.{u}) :
    relativeOpenImmersion S ≤ MorphismProperty.monomorphisms (Over S) := by
  intro X Y f hf
  let : IsOpenImmersion f.left := hf
  exact Over.mono_of_mono_left f

namespace RelativeRepresentability

variable {S : Scheme.{u}}
  (F : Sheaf (Scheme.zariskiTopology.over S) (Type u))
  {ι : Type u} {X : ι → Over S}
  (f : ∀ i, yoneda.obj (X i) ⟶ F.obj)
  (hf : ∀ i, (relativeOpenImmersion S).presheaf (f i))

open Functor.relativelyRepresentable

/-- Cyclic permutation of the three local representatives on a triple overlap. -/
def tripleTransition (i j k : ι) :
    (hf i).rep.pullback₃ (f j) (f k) ⟶ (hf j).rep.pullback₃ (f k) (f i) :=
  (hf j).rep.lift₃ (f k) (f i)
    (pullback₃.p₂ (hf i).rep (f j) (f k))
    (pullback₃.p₃ (hf i).rep (f j) (f k))
    (pullback₃.p₁ (hf i).rep (f j) (f k))
    ((pullback₃.map_p₂_comp (hf i).rep (f j) (f k)).trans
      (pullback₃.map_p₃_comp (hf i).rep (f j) (f k)).symm)
    ((pullback₃.map_p₂_comp (hf i).rep (f j) (f k)).trans
      (pullback₃.map_p₁_comp (hf i).rep (f j) (f k)).symm)

@[reassoc]
theorem tripleTransition_p₁ (i j k : ι) :
    tripleTransition F f hf i j k ≫ pullback₃.p₁ (hf j).rep (f k) (f i) =
      pullback₃.p₂ (hf i).rep (f j) (f k) :=
  lift₃_p₁ _ _ _ _ _ _ _ _

@[reassoc]
theorem tripleTransition_p₂ (i j k : ι) :
    tripleTransition F f hf i j k ≫ pullback₃.p₂ (hf j).rep (f k) (f i) =
      pullback₃.p₃ (hf i).rep (f j) (f k) :=
  lift₃_p₂ _ _ _ _ _ _ _ _

@[reassoc]
theorem tripleTransition_p₃ (i j k : ι) :
    tripleTransition F f hf i j k ≫ pullback₃.p₃ (hf j).rep (f k) (f i) =
      pullback₃.p₁ (hf i).rep (f j) (f k) :=
  lift₃_p₃ _ _ _ _ _ _ _ _

/-- Cyclic transition maps satisfy the cocycle identity. -/
theorem tripleTransition_cocycle (i j k : ι) :
    tripleTransition F f hf i j k ≫ tripleTransition F f hf j k i ≫
      tripleTransition F f hf k i j = 𝟙 _ := by
  apply pullback₃.hom_ext
  · simp only [Category.assoc, tripleTransition_p₁, tripleTransition_p₂,
      tripleTransition_p₃, Category.id_comp]
  · simp only [Category.assoc, tripleTransition_p₁, tripleTransition_p₂,
      tripleTransition_p₃, Category.id_comp]
  · simp only [Category.assoc, tripleTransition_p₁, tripleTransition_p₂,
      tripleTransition_p₃, Category.id_comp]

/-- Locally represented open pieces and their represented intersections
give gluing data in the category over the original base. -/
@[simps]
def glueData : RelativeGluing.Construction.Schemes.RelativeGlueData S where
  J := ι
  U := X
  V ij := (hf ij.1).rep.pullback (f ij.2)
  f i j := (hf i).rep.fst' (f j)
  f_mono i j := by
    have h := (hf j).property _ _ _ ((hf i).rep.isPullback' (f j)).flip
    exact relativeOpenImmersion_le_monomorphisms S _ h
  f_id i := (relativeOpenImmersion S).isIso_fst'_self
    (relativeOpenImmersion_le_monomorphisms S) (hf i)
  t i j := (hf i).rep.symmetry (hf j).rep
  t_id i := by
    apply (hf i).rep.hom_ext'
    · simp [(relativeOpenImmersion S).fst'_self_eq_snd
        (relativeOpenImmersion_le_monomorphisms S) (hf i)]
    · simp [(relativeOpenImmersion S).fst'_self_eq_snd
        (relativeOpenImmersion_le_monomorphisms S) (hf i)]
  t' := tripleTransition F f hf
  t_fac i j k := by
    apply (hf j).rep.hom_ext'
    · simp only [Category.assoc, symmetry_fst, pullback₃.fst_snd_eq_p₂]
      exact (Category.assoc (tripleTransition F f hf i j k)
        (pullback.snd _ _) ((hf j).rep.fst' (f i))).trans
        ((congrArg (fun p => tripleTransition F f hf i j k ≫ p)
          (pullback₃.snd_fst'_eq_p₁ (hf j).rep (f k) (f i))).trans
          (tripleTransition_p₁ F f hf i j k))
    · simp only [Category.assoc, symmetry_snd, pullback₃.fst_fst'_eq_p₁]
      exact (Category.assoc (tripleTransition F f hf i j k)
        (pullback.snd _ _) ((hf j).rep.snd (f i))).trans
        (tripleTransition_p₃ F f hf i j k)
  cocycle := tripleTransition_cocycle F f hf
  f_open i j := (hf j).property _ _ _ ((hf i).rep.isPullback' (f j)).flip

/-- The inclusion of a locally represented piece into the relative gluing. -/
def toGlued (i : ι) : X i ⟶ (glueData F f hf).glued :=
  (glueData F f hf).toGlueData.ι i

/-- The local universal sections agree on their represented intersections. -/
theorem chartSections_compatible (i j : ι) :
    F.obj.map ((hf i).rep.fst' (f j)).op (yonedaEquiv (f i)) =
      F.obj.map (((hf j).rep.fst' (f i)).op ≫ ((hf i).rep.symmetry (hf j).rep).op)
        (yonedaEquiv (f j)) := by
  apply yonedaEquiv.symm.injective
  rw [yonedaEquiv_naturality, Equiv.symm_apply_apply,
    Functor.map_comp_apply, yonedaEquiv_naturality, yonedaEquiv_naturality,
    Equiv.symm_apply_apply, ← Functor.map_comp_assoc,
    Functor.relativelyRepresentable.symmetry_fst, ((hf i).rep.isPullback' (f j)).w]

/-- The locally specified universal sections glue to a natural morphism
from the point sheaf of the relative glued scheme. -/
def yonedaGluedToSheaf :
    (Scheme.zariskiTopology.over S).yoneda.obj (glueData F f hf).glued ⟶ F where
  hom := yonedaEquiv.symm <| (glueData F f hf).sheafValGluedMk
    (fun i => yonedaEquiv (f i)) (chartSections_compatible F f hf)

/-- The global morphism agrees with each prescribed local representation. -/
theorem yoneda_toGlued_yonedaGluedToSheaf (i : ι) :
    yoneda.map (toGlued F f hf i) ≫ (yonedaGluedToSheaf F f hf).hom = f i := by
  apply yonedaEquiv.injective
  rw [yonedaGluedToSheaf, yonedaEquiv_apply, yonedaEquiv_apply,
    NatTrans.comp_app_apply, yoneda_map_app]
  exact (glueData F f hf).sheafValGluedMk_val _ _ i

/-- Two local lifts of the same sheaf section determine the same map
to the glued scheme. -/
theorem comp_toGlued_eq {U : Over S} {i j : ι} (a : U ⟶ X i) (b : U ⟶ X j)
    (h : yoneda.map a ≫ f i = yoneda.map b ≫ f j) :
    a ≫ toGlued F f hf i = b ≫ toGlued F f hf j := by
  rw [← (hf i).rep.lift'_fst a b h, Category.assoc]
  conv_rhs => rw [← (hf i).rep.lift'_snd a b h, Category.assoc]
  congr 1
  exact ((glueData F f hf).toGlueData.glue_condition i j).symm.trans
    ((Category.assoc ((hf i).rep.symmetry (hf j).rep)
      ((hf j).rep.fst' (f i)) (toGlued F f hf j)).symm.trans
      (congrArg (fun k => k ≫ toGlued F f hf j) (symmetry_fst (hf i).rep (hf j).rep)))

/-- The global map evaluated on a map through a chart is the local
universal section evaluated on that map. -/
theorem yonedaGluedToSheaf_app_chart {U : Over S} {i : ι} (a : U ⟶ X i) :
    (yonedaGluedToSheaf F f hf).hom.app (op U) (a ≫ toGlued F f hf i) =
      yonedaEquiv (yoneda.map a ≫ f i) := by
  have he := (congrArg (fun k => k ≫ (yonedaGluedToSheaf F f hf).hom)
    (yoneda.map_comp a (toGlued F f hf i))).trans
    ((Category.assoc (yoneda.map a) (yoneda.map (toGlued F f hf i))
      (yonedaGluedToSheaf F f hf).hom).trans
      (congrArg (fun k => yoneda.map a ≫ k)
        (yoneda_toGlued_yonedaGluedToSheaf F f hf i)))
  have h := congrArg yonedaEquiv he
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map] at h
  exact h

instance yonedaGluedToSheaf_locallySurjective
    [Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S) (Sigma.desc f)] :
    Sheaf.IsLocallySurjective (yonedaGluedToSheaf F f hf) :=
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
    (show Sigma.desc (fun i => yoneda.map (toGlued F f hf i)) ≫
      (yonedaGluedToSheaf F f hf).hom = Sigma.desc f by
      apply Sigma.hom_ext
      intro i
      simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
      exact yoneda_toGlued_yonedaGluedToSheaf F f hf i)

instance yonedaGluedToSheaf_locallyInjective :
    Sheaf.IsLocallyInjective (yonedaGluedToSheaf F f hf) where
  equalizerSieve_mem := by
    rintro ⟨U⟩ (α β : U ⟶ _) h
    let J := Scheme.zariskiTopology.over S
    have hcover := (glueData F f hf).charts_covering
    refine J.superset_covering ?_
      (J.intersection_covering (J.pullback_stable α hcover) (J.pullback_stable β hcover))
    rintro V (γ : V ⟶ U) ⟨⟨W₁, a, _, ⟨i⟩, fac₁⟩, ⟨W₂, b, _, ⟨j⟩, fac₂⟩⟩
    change γ ≫ α = γ ≫ β
    have hn : (yonedaGluedToSheaf F f hf).hom.app (op V) (γ ≫ α) =
        (yonedaGluedToSheaf F f hf).hom.app (op V) (γ ≫ β) := by
      have hα := (yonedaGluedToSheaf F f hf).hom.naturality_apply γ.op α
      have hβ := (yonedaGluedToSheaf F f hf).hom.naturality_apply γ.op β
      exact hα.trans ((congrArg (fun x => F.obj.map γ.op x) h).trans hβ.symm)
    rw [← fac₁, ← fac₂] at hn ⊢
    apply comp_toGlued_eq F f hf
    apply yonedaEquiv.injective
    exact (yonedaGluedToSheaf_app_chart F f hf a).symm.trans
      (hn.trans (yonedaGluedToSheaf_app_chart F f hf b))

/-- A sheaf covered by relatively representable open subfunctors is
represented by the relative scheme obtained by gluing those pieces. -/
theorem yonedaGluedToSheaf_isIso
    [Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S) (Sigma.desc f)] :
    IsIso (yonedaGluedToSheaf F f hf) := by
  rw [← Sheaf.isLocallyBijective_iff_isIso (yonedaGluedToSheaf F f hf)]
  constructor <;> infer_instance

/-- The relative glued scheme represents the sheaf with its specified
local universal sections. -/
def representableBy
    [Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S) (Sigma.desc f)] :
    F.obj.RepresentableBy (glueData F f hf).glued := by
  let e := @asIso _ _ _ _ (yonedaGluedToSheaf F f hf)
    (yonedaGluedToSheaf_isIso F f hf)
  exact Functor.representableByEquiv.symm ((sheafToPresheaf _ _).mapIso e)

include hf in
/-- Representability of a sheaf is local for relatively representable
open covers in the category of schemes over a fixed base. -/
theorem isRepresentable
    [Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S) (Sigma.desc f)] :
    F.obj.IsRepresentable :=
  ⟨(glueData F f hf).glued, ⟨representableBy F f hf⟩⟩

end RelativeRepresentability

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeRepresentabilityP.Construction.Schemes
