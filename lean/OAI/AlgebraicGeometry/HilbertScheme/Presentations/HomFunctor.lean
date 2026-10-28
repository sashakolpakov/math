import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Functor
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Hom Functor -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.HomFunctor.Hom

noncomputable section

/-!
The relative morphism functor and its scheme-theoretic graphs. A T-point is
an S-morphism T ×_S X → Y, canonically the same data as a T-morphism X_T → Y_T.
These definitions contain no representability assumption.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (X Y : Over S)

def morphismFunctor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := T.unop ⨯ X ⟶ Y
  map a := ↾fun f => prod.map a.unop (𝟙 X) ≫ f
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro f
    change prod.map (𝟙 T.unop) (𝟙 X) ≫ f = f
    rw [prod.map_id_id, Category.id_comp]
  map_comp a b := by
    apply ConcreteCategory.hom_ext
    intro f
    change prod.map (b.unop ≫ a.unop) (𝟙 X) ≫ f =
      prod.map b.unop (𝟙 X) ≫ (prod.map a.unop (𝟙 X) ≫ f)
    rw [← Category.assoc, prod.map_map, Category.id_comp]

/-- The T-relative morphism associated with an S-morphism T ×_S X → Y. -/
def overTestMorphism {T : Over S} (f : T ⨯ X ⟶ Y) : T ⨯ X ⟶ T ⨯ Y :=
  prod.lift prod.fst f

theorem overTestMorphism_fst {T : Over S} (f : T ⨯ X ⟶ Y) :
    overTestMorphism X Y f ≫ prod.fst = prod.fst :=
  prod.lift_fst _ _

theorem overTestMorphism_snd {T : Over S} (f : T ⨯ X ⟶ Y) :
    overTestMorphism X Y f ≫ prod.snd = f :=
  prod.lift_snd _ _

/-- The equality expressing that a map lies over T is the only extra datum. -/
def overTestMorphismEquiv (T : Over S) :
    (T ⨯ X ⟶ Y) ≃
      {f : T ⨯ X ⟶ T ⨯ Y // f ≫ prod.fst = prod.fst} where
  toFun f := ⟨overTestMorphism X Y f, overTestMorphism_fst X Y f⟩
  invFun f := f.val ≫ prod.snd
  left_inv f := overTestMorphism_snd X Y f
  right_inv f := by
    apply Subtype.ext
    apply prod.hom_ext
    · exact (prod.lift_fst _ _).trans f.property.symm
    · exact prod.lift_snd _ _

/-- Graph inclusion, with ambient space T ×_S (X ×_S Y). -/
def graph {T : Over S} (f : T ⨯ X ⟶ Y) : T ⨯ X ⟶ T ⨯ (X ⨯ Y) :=
  prod.lift prod.fst (prod.lift prod.snd f)

def graphProjection (T : Over S) : T ⨯ (X ⨯ Y) ⟶ T ⨯ X :=
  prod.map (𝟙 T) prod.fst

theorem graph_projection {T : Over S} (f : T ⨯ X ⟶ Y) :
    graph X Y f ≫ graphProjection X Y T = 𝟙 (T ⨯ X) := by
  apply prod.hom_ext
  · simp only [graph, graphProjection, Category.assoc, prod.map_fst,
      prod.lift_fst, Category.comp_id, Category.id_comp]
  · simp only [graph, graphProjection, Category.assoc, prod.map_snd,
      prod.lift_snd_assoc, prod.lift_fst, Category.id_comp]

theorem graph_baseChange {T U : Over S} (a : T ⟶ U) (f : U ⨯ X ⟶ Y) :
    graph X Y (prod.map a (𝟙 X) ≫ f) ≫ prod.map a (𝟙 (X ⨯ Y)) =
      prod.map a (𝟙 X) ≫ graph X Y f := by
  apply prod.hom_ext
  · simp only [graph, Category.assoc, prod.map_fst, prod.lift_fst_assoc,
      prod.lift_fst]
  · apply prod.hom_ext
    · simp only [graph, Category.assoc, prod.map_snd, prod.lift_snd_assoc,
        prod.lift_fst, Category.comp_id]
    · simp only [graph, Category.assoc, prod.map_snd,
        prod.lift_snd, Category.comp_id]

private theorem separated_graph {B V W : Scheme.{u}} (p : V ⟶ B) (q : W ⟶ B)
    [IsSeparated q] (f : V ⟶ W) (hf : f ≫ q = p) :
    IsClosedImmersion (pullback.lift (𝟙 V) f (by simpa using hf.symm)) := by
  subst p
  exact inferInstanceAs
    (IsClosedImmersion (pullback.lift (𝟙 V) f (Category.id_comp (f ≫ q))))

/-- The graph is a closed immersion for a separated target. -/
theorem graph_isClosedImmersion [IsSeparated Y.hom]
    {T : Over S} (f : T ⨯ X ⟶ Y) : IsClosedImmersion (graph X Y f).left := by
  let e : ((T ⨯ X) ⨯ Y) ≅ T ⨯ (X ⨯ Y) := prod.associator T X Y
  have hgraph : graph X Y f = prod.lift (𝟙 (T ⨯ X)) f ≫ e.hom := by
    apply prod.hom_ext
    · simp only [graph, e, Limits.prod.associator, Category.assoc,
        prod.lift_fst_assoc, prod.lift_fst, Category.id_comp]
    · apply prod.hom_ext
      · simp only [graph, e, Limits.prod.associator, Category.assoc,
          prod.lift_fst_assoc, prod.lift_snd_assoc, prod.lift_fst, Category.id_comp]
      · simp only [graph, e, Limits.prod.associator, Category.assoc,
          prod.lift_snd]
  rw [hgraph]
  change IsClosedImmersion
    ((prod.lift (𝟙 (T ⨯ X)) f).left ≫ e.hom.left)
  have : IsClosedImmersion (prod.lift (𝟙 (T ⨯ X)) f).left := by
    rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
      (Over.prodLeftIsoPullback (T ⨯ X) Y).hom]
    have hw : f.left ≫ Y.hom = (T ⨯ X).hom := f.w
    have h : (prod.lift (𝟙 (T ⨯ X)) f).left ≫
        (Over.prodLeftIsoPullback (T ⨯ X) Y).hom =
        pullback.lift (𝟙 (T ⨯ X).left) f.left (by simp) := by
      apply pullback.hom_ext
      · rw [Category.assoc, Over.prodLeftIsoPullback_hom_fst,
          ← Over.comp_left, prod.lift_fst, pullback.lift_fst]
        rfl
      · rw [Category.assoc, Over.prodLeftIsoPullback_hom_snd,
          ← Over.comp_left, prod.lift_snd, pullback.lift_snd]
    rw [h]
    exact separated_graph (T ⨯ X).hom Y.hom f.left hw
  have : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
  infer_instance

@[reassoc]
theorem graph_fst {T : Over S} (f : T ⨯ X ⟶ Y) :
    graph X Y f ≫ prod.fst = prod.fst :=
  prod.lift_fst _ _

@[reassoc]
theorem graph_snd_fst {T : Over S} (f : T ⨯ X ⟶ Y) :
    graph X Y f ≫ prod.snd ≫ prod.fst = prod.snd := by
  rw [graph, prod.lift_snd_assoc, prod.lift_fst]

@[reassoc]
theorem graph_snd_snd {T : Over S} (f : T ⨯ X ⟶ Y) :
    graph X Y f ≫ prod.snd ≫ prod.snd = f := by
  rw [graph, prod.lift_snd_assoc, prod.lift_snd]

theorem graphProjection_naturality {T U : Over S} (a : T ⟶ U) :
    graphProjection X Y T ≫ prod.map a (𝟙 X) =
      prod.map a (𝟙 (X ⨯ Y)) ≫ graphProjection X Y U := by
  dsimp [graphProjection]
  rw [prod.map_map, prod.map_map, Category.id_comp, Category.comp_id,
    Category.id_comp, Category.comp_id]

/-- Graphs commute with base change through an actual cartesian square. -/
theorem graph_isPullback {T U : Over S} (a : T ⟶ U) (f : U ⨯ X ⟶ Y) :
    IsPullback (graph X Y (prod.map a (𝟙 X) ≫ f)) (prod.map a (𝟙 X))
      (prod.map a (𝟙 (X ⨯ Y))) (graph X Y f) where
  w := graph_baseChange X Y a f
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s => by
    let l := s.fst ≫ graphProjection X Y T
    have hl : l ≫ prod.map a (𝟙 X) = s.snd := by
      dsimp [l]
      rw [Category.assoc, graphProjection_naturality, ← Category.assoc,
        s.condition, Category.assoc, graph_projection, Category.comp_id]
    refine ⟨l, ?_, hl, ?_⟩
    · change l ≫ graph X Y (prod.map a (𝟙 X) ≫ f) = s.fst
      apply prod.hom_ext
      · dsimp [l]
        rw [Category.assoc, graph_fst]
        simp only [graphProjection, Category.assoc, prod.map_fst, Category.comp_id]
      · apply prod.hom_ext
        · dsimp [l]
          simp only [Category.assoc, graph_snd_fst]
          simp only [graphProjection, prod.map_snd]
        · simp only [Category.assoc, graph_snd_snd]
          rw [← Category.assoc, hl]
          have h := congrArg (fun k => k ≫ prod.snd ≫ prod.snd) s.condition
          simpa only [Category.assoc, prod.map_snd_assoc, Category.id_comp,
            graph_snd_snd] using h.symm
    · intro m hm _
      change s.pt ⟶ T ⨯ X at m
      change m ≫ graph X Y (prod.map a (𝟙 X) ≫ f) = s.fst at hm
      change m = l
      calc
        m = m ≫ (graph X Y (prod.map a (𝟙 X) ≫ f) ≫ graphProjection X Y T) := by
          rw [graph_projection, Category.comp_id]
        _ = l := by rw [← Category.assoc, hm])⟩

def graphIdeal {T : Over S} (f : T ⨯ X ⟶ Y) :
    (Hilbert.Functor.ambient (X ⨯ Y) T).IdealSheafData :=
  (graph X Y f).left.ker

theorem graph_image_projection {T : Over S} (f : T ⨯ X ⟶ Y) :
    (graph X Y f).left.toImage ≫ Hilbert.Functor.familyProjection (X ⨯ Y) (graphIdeal X Y f) =
      Hilbert.Functor.ambientProjection X T := by
  change (graph X Y f).left.toImage ≫
    ((graph X Y f).left.imageι ≫ (prod.fst : T ⨯ (X ⨯ Y) ⟶ T).left) = _
  rw [← Category.assoc, Scheme.Hom.toImage_imageι, ← Over.comp_left, graph_fst]
  rfl

/-- Every graph belongs to the genuine Hilbert-family functor when the
source is flat, proper and finitely presented over the base. -/
theorem graph_isFamily [Flat X.hom] [IsProper X.hom]
    [LocallyOfFinitePresentation X.hom] [IsSeparated Y.hom]
    {T : Over S} (f : T ⨯ X ⟶ Y) :
    Hilbert.Functor.IsFamily (X ⨯ Y) (graphIdeal X Y f) := by
  have : IsClosedImmersion (graph X Y f).left := graph_isClosedImmersion X Y f
  have : IsIso (graph X Y f).left.toImage := inferInstance
  have hpFlat : Flat (Hilbert.Functor.ambientProjection X T) := by
    change Flat (prod.fst : T ⨯ X ⟶ T).left
    rw [← Over.prodLeftIsoPullback_hom_fst]
    infer_instance
  have hpProper : IsProper (Hilbert.Functor.ambientProjection X T) := by
    change IsProper (prod.fst : T ⨯ X ⟶ T).left
    rw [← Over.prodLeftIsoPullback_hom_fst]
    infer_instance
  have hpFP : LocallyOfFinitePresentation (Hilbert.Functor.ambientProjection X T) := by
    change LocallyOfFinitePresentation (prod.fst : T ⨯ X ⟶ T).left
    rw [← Over.prodLeftIsoPullback_hom_fst]
    infer_instance
  have heq : Hilbert.Functor.familyProjection (X ⨯ Y) (graphIdeal X Y f) =
      inv (graph X Y f).left.toImage ≫ Hilbert.Functor.ambientProjection X T :=
    (Iso.eq_inv_comp (asIso (graph X Y f).left.toImage)).mpr
      (graph_image_projection X Y f)
  let := hpFlat
  let := hpProper
  let := hpFP
  have hiIso : IsIso (inv (graph X Y f).left.toImage) :=
    (asIso (graph X Y f).left.toImage).isIso_inv
  let := hiIso
  have hiFlat : Flat (inv (graph X Y f).left.toImage) := inferInstance
  have hiProper : IsProper (inv (graph X Y f).left.toImage) := inferInstance
  have hiFP : LocallyOfFinitePresentation (inv (graph X Y f).left.toImage) := inferInstance
  let := hiFlat
  let := hiProper
  let := hiFP
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    exact @Flat.comp _ _ _ _ _ hiFlat hpFlat
  · rw [heq]
    exact MorphismProperty.comp_mem (@IsProper) _ _ hiProper hpProper
  · rw [heq]
    exact @locallyOfFinitePresentation_comp _ _ _ _ _ hiFP hpFP

def graphFamily [Flat X.hom] [IsProper X.hom] [LocallyOfFinitePresentation X.hom]
    [IsSeparated Y.hom] {T : Over S} (f : T ⨯ X ⟶ Y) : Hilbert.Functor.Family (X ⨯ Y) T :=
  ⟨graphIdeal X Y f, graph_isFamily X Y f⟩

theorem graphIdeal_baseChange [IsSeparated Y.hom]
    {T U : Over S} (a : T ⟶ U) (f : U ⨯ X ⟶ Y) :
    graphIdeal X Y (prod.map a (𝟙 X) ≫ f) =
      (graphIdeal X Y f).comap (Hilbert.Functor.ambientMap (X ⨯ Y) a) := by
  have : IsClosedImmersion (graph X Y f).left := graph_isClosedImmersion X Y f
  let H : IsPullback (graph X Y (prod.map a (𝟙 X) ≫ f)).left
      (prod.map a (𝟙 X)).left (prod.map a (𝟙 (X ⨯ Y))).left (graph X Y f).left :=
    (graph_isPullback X Y a f).map (Over.forget S)
  have : IsIso H.isoPullback.hom := H.isoPullback.isIso_hom
  change (graph X Y (prod.map a (𝟙 X) ≫ f)).left.ker =
    (graph X Y f).left.ker.comap (prod.map a (𝟙 (X ⨯ Y))).left
  rw [← H.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

theorem graphFamily_baseChange [Flat X.hom] [IsProper X.hom]
    [LocallyOfFinitePresentation X.hom] [IsSeparated Y.hom]
    {T U : Over S} (a : T ⟶ U) (f : U ⨯ X ⟶ Y) :
    graphFamily X Y (prod.map a (𝟙 X) ≫ f) =
      Hilbert.Functor.pullbackFamily (X ⨯ Y) a (graphFamily X Y f) :=
  Subtype.ext (graphIdeal_baseChange X Y a f)

/-- The natural graph transformation into the actual relative Hilbert functor. -/
def graphs [Flat X.hom] [IsProper X.hom] [LocallyOfFinitePresentation X.hom]
    [IsSeparated Y.hom] :
    morphismFunctor X Y ⟶ Hilbert.Functor.familyFunctor (X ⨯ Y) where
  app T := ↾fun f => graphFamily X Y f
  naturality := by
    intro T U a
    apply ConcreteCategory.hom_ext
    intro f
    exact graphFamily_baseChange X Y a.unop f

/-- A closed graph ideal determines the morphism, including on nonreduced bases. -/
theorem graphIdeal_injective [IsSeparated Y.hom] (T : Over S) :
    Function.Injective (graphIdeal X Y (T := T)) := by
  intro f g h
  have hf : IsClosedImmersion (graph X Y f).left := graph_isClosedImmersion X Y f
  have hg : IsClosedImmersion (graph X Y g).left := graph_isClosedImmersion X Y g
  let := hf
  let := hg
  have hker : (graph X Y g).left.ker ≤ (graph X Y f).left.ker := h.symm.le
  let a := IsClosedImmersion.lift (graph X Y g).left (graph X Y f).left hker
  have ha : a ≫ (graph X Y g).left = (graph X Y f).left :=
    IsClosedImmersion.lift_fac _ _ _
  have hpf : (graph X Y f).left ≫ (graphProjection X Y T).left = 𝟙 _ := by
    rw [← Over.comp_left, graph_projection]
    rfl
  have hpg : (graph X Y g).left ≫ (graphProjection X Y T).left = 𝟙 _ := by
    rw [← Over.comp_left, graph_projection]
    rfl
  have hai : a = 𝟙 _ := by
    calc
      a = a ≫ ((graph X Y g).left ≫ (graphProjection X Y T).left) := by
        rw [hpg, Category.comp_id]
      _ = 𝟙 _ := by rw [← Category.assoc, ha, hpf]
  have hgraphs : (graph X Y f).left = (graph X Y g).left := by
    rw [hai, Category.id_comp] at ha
    exact ha.symm
  apply (Over.forget S).map_injective
  change f.left = g.left
  have hY := congrArg
    (fun i => i ≫ (prod.snd : T ⨯ (X ⨯ Y) ⟶ X ⨯ Y).left ≫
      (prod.snd : X ⨯ Y ⟶ Y).left) hgraphs
  simpa only [← Over.comp_left, graph_snd_snd] using hY

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.HomFunctor.Hom
