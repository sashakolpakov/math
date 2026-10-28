import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CoefficientLineDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Isomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Coefficient Line Descent -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines

noncomputable section

/-! Finite-coefficient descent of an actual line bundle on the
ordinary base change of a proper model. The recovery isomorphism
uses the actual coefficient projection, with both pullback orders
identified explicitly. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CoefficientLineDescent

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    (X : Over (Spec (.of R)))

abbrev genericBase : Spec (.of B) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R B))

abbrev stageBase (s : Finset B) : Spec (.of (AbelianModuli.ReferenceFamily.Finite.CoefficientDiagram.finiteCoefficientRing R B s)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (AbelianModuli.ReferenceFamily.Finite.CoefficientDiagram.finiteCoefficientRing R B s)))

abbrev stageProjection (s : Finset B) : Spec (.of B) ⟶ Spec (.of (AbelianModuli.ReferenceFamily.Finite.CoefficientDiagram.finiteCoefficientRing R B s)) :=
  Spec.map (CommRingCat.ofHom (AbelianModuli.ReferenceFamily.Finite.CoefficientDiagram.finiteCoefficientRing R B s).val.toRingHom)

theorem stageProjection_base (s : Finset B) :
    stageProjection R B s ≫ stageBase R B s = genericBase R B := by
  rw [stageProjection, stageBase, ← Spec.map_comp]
  rfl

def genericFlip : (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.finiteCoefficientFamilyCone R B X).pt ≅
    ((Over.pullback (genericBase R B)).obj X).left :=
  pullbackSymmetry (genericBase R B) X.hom

def stageFlip (s : Finset B) : (AbelianModuli.ReferenceFamily.Finite.CoefficientFrames.finiteCoefficientFamilyDiagram R B X).obj (.op s) ≅
    ((Over.pullback (stageBase R B s)).obj X).left :=
  pullbackSymmetry (stageBase R B s) X.hom

def modelProjection (s : Finset B) :
    ((Over.pullback (genericBase R B)).obj X).left ⟶
      ((Over.pullback (stageBase R B s)).obj X).left :=
  pullback.map X.hom (genericBase R B) X.hom (stageBase R B s)
    (𝟙 X.left) (stageProjection R B s) (𝟙 _) (by simp)
    (by simpa only [Category.comp_id] using (stageProjection_base R B s).symm)

theorem modelProjection_fst (s : Finset B) :
    modelProjection R B X s ≫ pullback.fst X.hom (stageBase R B s) =
      pullback.fst X.hom (genericBase R B) := by
  simp only [modelProjection, pullback.map, pullback.lift_fst, Category.comp_id]

theorem modelProjection_snd (s : Finset B) :
    modelProjection R B X s ≫ pullback.snd X.hom (stageBase R B s) =
      pullback.snd X.hom (genericBase R B) ≫ stageProjection R B s := by
  simp only [modelProjection, pullback.map, pullback.lift_snd]

theorem modelProjection_cartesian (s : Finset B) :
    IsPullback (modelProjection R B X s) (pullback.snd X.hom (genericBase R B))
      (pullback.snd X.hom (stageBase R B s)) (stageProjection R B s) := by
  have houter : IsPullback
      (modelProjection R B X s ≫ pullback.fst X.hom (stageBase R B s))
      (pullback.snd X.hom (genericBase R B)) X.hom
      (stageProjection R B s ≫ stageBase R B s) := by
    rw [modelProjection_fst, stageProjection_base]
    exact IsPullback.of_hasPullback _ _
  exact houter.of_right (modelProjection_snd R B X s) (IsPullback.of_hasPullback _ _)

theorem coefficientProjection_flip (s : Finset B) :
    (genericFlip R B X).hom ≫ modelProjection R B X s =
      (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.finiteCoefficientFamilyCone R B X).π.app (.op s) ≫ (stageFlip R B X s).hom := by
  have hg₁ : (genericFlip R B X).hom ≫ pullback.fst X.hom (genericBase R B) =
      pullback.snd (genericBase R B) X.hom :=
    pullbackSymmetry_hom_comp_fst (genericBase R B) X.hom
  have hs₁ : (stageFlip R B X s).hom ≫ pullback.fst X.hom (stageBase R B s) =
      pullback.snd (stageBase R B s) X.hom :=
    pullbackSymmetry_hom_comp_fst (stageBase R B s) X.hom
  have hg₂ : (genericFlip R B X).hom ≫ pullback.snd X.hom (genericBase R B) =
      pullback.fst (genericBase R B) X.hom :=
    pullbackSymmetry_hom_comp_snd (genericBase R B) X.hom
  have hs₂ : (stageFlip R B X s).hom ≫ pullback.snd X.hom (stageBase R B s) =
      pullback.fst (stageBase R B s) X.hom :=
    pullbackSymmetry_hom_comp_snd (stageBase R B s) X.hom
  apply pullback.hom_ext
  · rw [Category.assoc, modelProjection_fst, hg₁, Category.assoc, hs₁]
    exact (((Over.pullback X.hom).map
      ((AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.finiteCoefficientOverCone R B).π.app (.op s))).w).symm
  · rw [Category.assoc, modelProjection_snd, ← Category.assoc, hg₂, Category.assoc, hs₂]
    exact (AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange.overPullback_map_isPullback
      ((AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.finiteCoefficientOverCone R B).π.app (.op s)) X.hom).w

theorem coefficientProjection_inv_flip (s : Finset B) :
    modelProjection R B X s ≫ (stageFlip R B X s).inv =
      (genericFlip R B X).inv ≫ (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.finiteCoefficientFamilyCone R B X).π.app (.op s) := by
  apply (cancel_epi (genericFlip R B X).hom).mp
  rw [← Category.assoc, coefficientProjection_flip, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

theorem exists_line_stage [IsNoetherianRing R] [IsProper X.hom]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback (genericBase R B)).obj X).left) :
    ∃ (s : Finset B) (K : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback (stageBase R B s)).obj X).left),
      Nonempty ((K.pullback (modelProjection R B X s)).sheaf ≅ L.sheaf) := by
  let L' := L.pullback (genericFlip R B X).hom
  obtain ⟨s, K, ⟨e⟩⟩ := AbelianModuli.ReferenceFamily.Finite.CoefficientLineDescent.exists_finite_coefficient_line_model R B X L'
  refine ⟨s, K.pullback (stageFlip R B X s).inv, ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackComp (modelProjection R B X s) (stageFlip R B X s).inv).app K.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (coefficientProjection_inv_flip R B X s)).app K.sheaf ≪≫
    (Scheme.Modules.pullbackComp (genericFlip R B X).inv
      ((AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.finiteCoefficientFamilyCone R B X).π.app (.op s))).symm.app K.sheaf ≪≫
    (Scheme.Modules.pullback (genericFlip R B X).inv).mapIso e ≪≫
    (Scheme.Modules.pullbackComp (genericFlip R B X).inv (genericFlip R B X).hom).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (genericFlip R B X).inv_hom_id).app L.sheaf ≪≫
    (Scheme.Modules.pullbackId _).app L.sheaf

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines
