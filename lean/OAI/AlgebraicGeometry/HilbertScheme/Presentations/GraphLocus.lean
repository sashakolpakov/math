import OAI.AlgebraicGeometry.HilbertScheme.Presentations.HomFunctor

/-! # Graph Locus -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.GraphLocus.Hom

noncomputable section

/-!
The graph locus inside the actual closed-subscheme functor. Its condition is
that projection of the closed subscheme onto the source is an isomorphism.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (X Y : Over S)

def subschemeOver {T : Over S} (I : (Hilbert.Functor.ambient (X ⨯ Y) T).IdealSheafData) :
    Over S :=
  Over.mk (I.subschemeι ≫ (T ⨯ (X ⨯ Y)).hom)

def subschemeInclusion {T : Over S}
    (I : (Hilbert.Functor.ambient (X ⨯ Y) T).IdealSheafData) :
    subschemeOver X Y I ⟶ T ⨯ (X ⨯ Y) :=
  Over.homMk I.subschemeι rfl

def subschemeProjection {T : Over S}
    (I : (Hilbert.Functor.ambient (X ⨯ Y) T).IdealSheafData) :
    subschemeOver X Y I ⟶ T ⨯ X :=
  subschemeInclusion X Y I ≫ HomFunctor.Hom.graphProjection X Y T

def recoverMorphism {T : Over S}
    (I : (Hilbert.Functor.ambient (X ⨯ Y) T).IdealSheafData)
    [IsIso (subschemeProjection X Y I)] : T ⨯ X ⟶ Y :=
  inv (subschemeProjection X Y I) ≫ subschemeInclusion X Y I ≫ prod.snd ≫ prod.snd

theorem graph_recoverMorphism {T : Over S}
    (I : (Hilbert.Functor.ambient (X ⨯ Y) T).IdealSheafData)
    [IsIso (subschemeProjection X Y I)] :
    HomFunctor.Hom.graph X Y (recoverMorphism X Y I) =
      inv (subschemeProjection X Y I) ≫ subschemeInclusion X Y I := by
  apply prod.hom_ext
  · rw [HomFunctor.Hom.graph_fst]
    have h := congrArg (fun k => k ≫ (prod.fst : T ⨯ X ⟶ T))
      (IsIso.inv_hom_id (subschemeProjection X Y I))
    simpa only [subschemeProjection, HomFunctor.Hom.graphProjection, Category.assoc, prod.map_fst,
      Category.comp_id, Category.id_comp] using h.symm
  · apply prod.hom_ext
    · simp only [Category.assoc, HomFunctor.Hom.graph_snd_fst]
      have h := congrArg (fun k => k ≫ (prod.snd : T ⨯ X ⟶ X))
        (IsIso.inv_hom_id (subschemeProjection X Y I))
      simpa only [subschemeProjection, HomFunctor.Hom.graphProjection, Category.assoc, prod.map_snd,
        Category.id_comp] using h.symm
    · simp only [Category.assoc, HomFunctor.Hom.graph_snd_snd]
      rfl

theorem graphIdeal_recoverMorphism {T : Over S}
    (I : (Hilbert.Functor.ambient (X ⨯ Y) T).IdealSheafData)
    [IsIso (subschemeProjection X Y I)] :
    HomFunctor.Hom.graphIdeal X Y (recoverMorphism X Y I) = I := by
  have : IsIso (inv (subschemeProjection X Y I)).left :=
    ((Over.forget S).mapIso (asIso (subschemeProjection X Y I)).symm).isIso_hom
  change (HomFunctor.Hom.graph X Y (recoverMorphism X Y I)).left.ker = I
  rw [graph_recoverMorphism, Over.comp_left, Scheme.Hom.ker_comp_of_isIso]
  exact I.ker_subschemeι

theorem graphIdeal_projection_isIso [IsSeparated Y.hom]
    {T : Over S} (f : T ⨯ X ⟶ Y) :
    IsIso (subschemeProjection X Y (HomFunctor.Hom.graphIdeal X Y f)) := by
  have : IsClosedImmersion (HomFunctor.Hom.graph X Y f).left := HomFunctor.Hom.graph_isClosedImmersion X Y f
  have : IsIso (HomFunctor.Hom.graph X Y f).left.toImage := inferInstance
  apply (isIso_iff_of_reflects_iso _ (Over.forget S)).mp
  change IsIso ((HomFunctor.Hom.graph X Y f).left.imageι ≫ (HomFunctor.Hom.graphProjection X Y T).left)
  have h : (HomFunctor.Hom.graph X Y f).left.imageι ≫ (HomFunctor.Hom.graphProjection X Y T).left =
      inv (HomFunctor.Hom.graph X Y f).left.toImage := by
    apply (cancel_epi (HomFunctor.Hom.graph X Y f).left.toImage).mp
    rw [IsIso.hom_inv_id, ← Category.assoc, Scheme.Hom.toImage_imageι,
      ← Over.comp_left, HomFunctor.Hom.graph_projection]
    rfl
  rw [h]
  exact (asIso (HomFunctor.Hom.graph X Y f).left.toImage).isIso_inv

/-- Closed graph ideals are exactly the closed subschemes whose source
projection is an isomorphism; this is a scheme-theoretic classification. -/
def graphIdealEquiv [IsSeparated Y.hom] (T : Over S) :
    (T ⨯ X ⟶ Y) ≃
      {I : (Hilbert.Functor.ambient (X ⨯ Y) T).IdealSheafData //
        IsIso (subschemeProjection X Y I)} where
  toFun f := ⟨HomFunctor.Hom.graphIdeal X Y f, graphIdeal_projection_isIso X Y f⟩
  invFun I := letI := I.property; recoverMorphism X Y I.val
  left_inv f := by
    let := graphIdeal_projection_isIso X Y f
    exact HomFunctor.Hom.graphIdeal_injective X Y T (graphIdeal_recoverMorphism X Y (HomFunctor.Hom.graphIdeal X Y f))
  right_inv I := by
    let := I.property
    exact Subtype.ext (graphIdeal_recoverMorphism X Y I.val)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.GraphLocus.Hom
