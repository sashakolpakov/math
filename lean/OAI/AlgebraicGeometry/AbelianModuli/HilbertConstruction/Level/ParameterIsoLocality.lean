import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoidHomOpenLocality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackLevelCoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.GlobalSectionExt

/-! # Parameter Iso Locality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.ParameterIsoLocality

noncomputable section

/-! A comparison of two native parameter pullbacks is a group and
ordered-level isomorphism when this holds on an open cover. The local
comparisons are identified by their actual projection squares. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u v

private theorem section_transport_square {C : Type*} [Category* C]
    {V V' X X' Y Y' : C}
    (a : V' ⟶ V) (s : V ⟶ X) (t : V ⟶ Y) (s' : V' ⟶ X') (t' : V' ⟶ Y')
    (p : X' ⟶ X) (q : Y' ⟶ Y) (e : X ⟶ Y) (e' : X' ⟶ Y')
    (hs : s' ≫ p = a ≫ s) (ht : t' ≫ q = a ≫ t)
    (hn : p ≫ e = e' ≫ q) (he : s' ≫ e' = t') :
    a ≫ (s ≫ e) = a ≫ t := by
  rw [← Category.assoc, ← hs, Category.assoc, hn, ← Category.assoc, he, ht]

private theorem conjugate_projection {C : Type*} [Category* C]
    {A A' B B' X Y : C}
    (a : A' ⟶ A) (b : B ⟶ B') (e : A ⟶ B)
    (p : B' ⟶ Y) (q : A' ⟶ X) (s : A ⟶ X) (t : B ⟶ Y) (v : X ⟶ Y)
    (hb : b ≫ p = t) (h : s ≫ v = e ≫ t) (ha : a ≫ s = q) :
    (a ≫ e ≫ b) ≫ p = q ≫ v := by
  calc
    _ = a ≫ (e ≫ (b ≫ p)) := by simp only [Category.assoc]
    _ = a ≫ (e ≫ t) := congrArg (fun k => a ≫ (e ≫ k)) hb
    _ = a ≫ (s ≫ v) := congrArg (fun k => a ≫ k) h.symm
    _ = (a ≫ s) ≫ v := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun k => k ≫ v) ha

private theorem monoid_bridge {B : Scheme.{u}} {X X' Y Y' : Over B}
    [MonObj X] [MonObj X'] [MonObj Y] [MonObj Y']
    (a : X ≅ X') (b : Y ≅ Y') (e : X ⟶ Y)
    [IsMonHom a.hom] [IsMonHom b.hom] [IsMonHom e] :
    IsMonHom (a.inv ≫ e ≫ b.hom) := by infer_instance

private theorem nativeParameterPullback_hom_eq
    {S T U : Scheme.{u}} (X : Over S) (a b : T ⟶ S) (u : U ⟶ T)
    (a' b' : U ⟶ S) (ha : u ≫ a = a') (hb : u ≫ b = b')
    (e : (Over.pullback a).obj X ≅ (Over.pullback b).obj X)
    (e' : (Over.pullback a').obj X ≅ (Over.pullback b').obj X)
    (h : Single.ParameterBaseChange.singleParameterBaseChangeMap
        (Over.homMk u ha : Over.mk a' ⟶ Over.mk a) X ≫ e.hom.left =
      e'.hom.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap
        (Over.homMk u hb : Over.mk b' ⟶ Over.mk b) X) :
    (Over.pullback u).map e.hom =
      (Single.ParameterBaseChange.singleParameterBaseChangeIso (Over.homMk u ha : Over.mk a' ⟶ Over.mk a) X).inv ≫
      e'.hom ≫ (Single.ParameterBaseChange.singleParameterBaseChangeIso (Over.homMk u hb : Over.mk b' ⟶ Over.mk b) X).hom := by
  let ca : Over.mk a' ⟶ Over.mk a := Over.homMk u ha
  let cb : Over.mk b' ⟶ Over.mk b := Over.homMk u hb
  let ea := Single.ParameterBaseChange.singleParameterBaseChangeIso ca X
  let eb := Single.ParameterBaseChange.singleParameterBaseChangeIso cb X
  have hR : (ea.inv.left ≫ e'.hom.left ≫ eb.hom.left) ≫
      pullback.fst ((Over.pullback b).obj X).hom u =
      pullback.fst ((Over.pullback a).obj X).hom u ≫ e.hom.left :=
    conjugate_projection ea.inv.left eb.hom.left e'.hom.left
      (pullback.fst ((Over.pullback b).obj X).hom u)
      (pullback.fst ((Over.pullback a).obj X).hom u)
      (Single.ParameterBaseChange.singleParameterBaseChangeMap ca X) (Single.ParameterBaseChange.singleParameterBaseChangeMap cb X) e.hom.left
      (Single.ParameterFunctoriality.singleParameterBaseChangeIso_hom_fst cb X) h (Single.ParameterFunctoriality.singleParameterBaseChangeIso_inv_comp ca X)
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (Pullback.Comparisons.overPullback_map_left_fst e.hom u).trans hR.symm
  · exact ((Over.pullback u).map e.hom).w.trans (ea.inv ≫ e'.hom ≫ eb.hom).w.symm

namespace AbelianScheme

variable {S T U : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

/-- Constant-label sections respect the original parameter-pullback
map, including when the structural composites are written differently. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.fullLevelGlobalSection_parameter (l : A.FullLevel N)
    {V W : Over S} (c : V ⟶ W)
    (z : Multiplicative (Fin (2 * g) → ZMod N)) :
    (A.pullback V.hom).fullLevelGlobalSection (l.pullback V.hom) z ≫
      Single.ParameterBaseChange.singleParameterBaseChangeMap c A.scheme =
        c.left ≫ (A.pullback W.hom).fullLevelGlobalSection (l.pullback W.hom) z := by
  let X := (Over.pullback V.hom).obj A.scheme
  let Y := (Over.pullback W.hom).obj A.scheme
  let s : V.left ⟶ X.left := (A.pullback V.hom).fullLevelGlobalSection (l.pullback V.hom) z
  let t : W.left ⟶ Y.left := (A.pullback W.hom).fullLevelGlobalSection (l.pullback W.hom) z
  have hs : s ≫ pullback.fst A.scheme.hom V.hom = V.hom ≫ A.fullLevelGlobalSection l z :=
    A.fullLevelGlobalSection_pullback l V.hom z
  have ht : t ≫ pullback.fst A.scheme.hom W.hom = W.hom ≫ A.fullLevelGlobalSection l z :=
    A.fullLevelGlobalSection_pullback l W.hom z
  have hs' : s ≫ X.hom = 𝟙 V.left :=
    (A.pullback V.hom).fullLevelGlobalSection_comp (l.pullback V.hom) z
  have ht' : t ≫ Y.hom = 𝟙 W.left :=
    (A.pullback W.hom).fullLevelGlobalSection_comp (l.pullback W.hom) z
  have hc : Single.ParameterBaseChange.singleParameterBaseChangeMap c A.scheme ≫ Y.hom = X.hom ≫ c.left :=
    Single.ParameterFunctoriality.singleParameterBaseChangeMap_over c A.scheme
  change s ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap c A.scheme = c.left ≫ t
  apply pullback.hom_ext
  · calc
      _ = V.hom ≫ A.fullLevelGlobalSection l z := by
        rw [Category.assoc, Single.ParameterBaseChange.singleParameterBaseChangeMap_comp, hs]
      _ = c.left ≫ (W.hom ≫ A.fullLevelGlobalSection l z) :=
        (congrArg (fun b => b ≫ A.fullLevelGlobalSection l z) c.w.symm).trans (Category.assoc _ _ _)
      _ = _ := (congrArg (fun k => c.left ≫ k) ht.symm).trans (Category.assoc _ _ _).symm
  · change (s ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap c A.scheme) ≫ Y.hom = (c.left ≫ t) ≫ Y.hom
    rw [Category.assoc, hc, ← Category.assoc, hs', Category.id_comp,
      Category.assoc, ht', Category.comp_id]

/-- A commuting native projection square identifies the ordinary
base change of the comparison with its conjugate by parameter isos. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.parameterPullback_hom_eq
    (a b : T ⟶ S) (u : U ⟶ T)
    (a' b' : U ⟶ S) (ha : u ≫ a = a') (hb : u ≫ b = b')
    (e : (A.pullback a).scheme ≅ (A.pullback b).scheme)
    (e' : (A.pullback a').scheme ≅ (A.pullback b').scheme)
    (h : Single.ParameterBaseChange.singleParameterBaseChangeMap
        (Over.homMk u ha : Over.mk a' ⟶ Over.mk a) A.scheme ≫ e.hom.left =
      e'.hom.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap
        (Over.homMk u hb : Over.mk b' ⟶ Over.mk b) A.scheme) :
    (Over.pullback u).map e.hom =
      (A.parameterPullbackIso (Over.homMk u ha : Over.mk a' ⟶ Over.mk a)).inv ≫
      e'.hom ≫
      (A.parameterPullbackIso (Over.homMk u hb : Over.mk b' ⟶ Over.mk b)).hom :=
  nativeParameterPullback_hom_eq A.scheme a b u a' b' ha hb e e' h

/-- Descent of both the group equations and the original ordered full
level through a cover, from concrete native comparison squares. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.fullLevelParameterIso_of_openCover
    (l : A.FullLevel N) (a b : T ⟶ S)
    (e : (A.pullback a).scheme ≅ (A.pullback b).scheme)
    (C : Scheme.OpenCover.{v} T)
    (a' b' : ∀ i, C.X i ⟶ S)
    (ha : ∀ i, C.f i ≫ a = a' i) (hb : ∀ i, C.f i ≫ b = b' i)
    (h : ∀ i, ∃ e' : (A.pullback (a' i)).scheme ≅ (A.pullback (b' i)).scheme,
      ∃ hg : IsMonHom e'.hom,
        letI := hg
        (l.pullback (a' i)).transport e' = l.pullback (b' i) ∧
        Single.ParameterBaseChange.singleParameterBaseChangeMap
          (Over.homMk (C.f i) (ha i) : Over.mk (a' i) ⟶ Over.mk a) A.scheme ≫ e.hom.left =
          e'.hom.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap
            (Over.homMk (C.f i) (hb i) : Over.mk (b' i) ⟶ Over.mk b) A.scheme) :
    ∃ hg : IsMonHom e.hom,
      letI := hg
      (l.pullback a).transport e = l.pullback b := by
  have hg : IsMonHom e.hom := by
    apply MonoidHomOpenLocality.isMonHom_of_openCover e.hom C
    intro i
    obtain ⟨e', he', hl, hn⟩ := h i
    let : IsMonHom e'.hom := he'
    let ca : Over.mk (a' i) ⟶ Over.mk a := Over.homMk (C.f i) (ha i)
    let cb : Over.mk (b' i) ⟶ Over.mk b := Over.homMk (C.f i) (hb i)
    let ea : (A.pullback (a' i)).scheme ≅ ((A.pullback a).pullback (C.f i)).scheme :=
      A.parameterPullbackIso ca
    let eb : (A.pullback (b' i)).scheme ≅ ((A.pullback b).pullback (C.f i)).scheme :=
      A.parameterPullbackIso cb
    let : IsMonHom ea.hom := Abelian.Schemes.AbelianScheme.parameterPullbackIso_isMonHom ca A
    let : IsMonHom eb.hom := Abelian.Schemes.AbelianScheme.parameterPullbackIso_isMonHom cb A
    have hm : IsMonHom (ea.inv ≫ e'.hom ≫ eb.hom) := monoid_bridge ea eb e'.hom
    have heq : (Over.pullback (C.f i)).map e.hom = ea.inv ≫ e'.hom ≫ eb.hom :=
      A.parameterPullback_hom_eq a b (C.f i) (a' i) (b' i) (ha i) (hb i) e e' hn
    exact (congrArg (fun k : ((A.pullback a).pullback (C.f i)).scheme ⟶
      ((A.pullback b).pullback (C.f i)).scheme => IsMonHom k) heq).mpr hm
  refine ⟨hg, ?_⟩
  let : IsMonHom e.hom := hg
  apply Abelian.Schemes.AbelianScheme.FullLevel.ext_globalSections
  intro z
  rw [Abelian.Schemes.AbelianScheme.fullLevelGlobalSection_transport]
  apply C.hom_ext
  intro i
  obtain ⟨e', he', hl, hn⟩ := h i
  let : IsMonHom e'.hom := he'
  let ca : Over.mk (a' i) ⟶ Over.mk a := Over.homMk (C.f i) (ha i)
  let cb : Over.mk (b' i) ⟶ Over.mk b := Over.homMk (C.f i) (hb i)
  have hz : (A.pullback (a' i)).fullLevelGlobalSection (l.pullback (a' i)) z ≫
      e'.hom.left = (A.pullback (b' i)).fullLevelGlobalSection (l.pullback (b' i)) z :=
    (Abelian.Schemes.AbelianScheme.fullLevelGlobalSection_transport (l.pullback (a' i)) e' z).symm.trans
      (congrArg (fun k => (A.pullback (b' i)).fullLevelGlobalSection k z) hl)
  exact section_transport_square (C.f i)
    ((A.pullback a).fullLevelGlobalSection (l.pullback a) z)
    ((A.pullback b).fullLevelGlobalSection (l.pullback b) z)
    ((A.pullback (a' i)).fullLevelGlobalSection (l.pullback (a' i)) z)
    ((A.pullback (b' i)).fullLevelGlobalSection (l.pullback (b' i)) z)
    (Single.ParameterBaseChange.singleParameterBaseChangeMap ca A.scheme) (Single.ParameterBaseChange.singleParameterBaseChangeMap cb A.scheme)
    e.hom.left e'.hom.left (A.fullLevelGlobalSection_parameter l ca z)
    (A.fullLevelGlobalSection_parameter l cb z) hn hz

end AbelianScheme

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.ParameterIsoLocality
