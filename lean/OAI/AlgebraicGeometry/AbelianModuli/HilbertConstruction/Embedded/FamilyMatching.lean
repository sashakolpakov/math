import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.OpenRefinement
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyGluing

/-! # Family Matching -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyMatching

noncomputable section

/-! Matching embedded families on any base open cover restrict to compatible directed descent data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (P T : Over S) (C : T.left.OpenCover)

/-- The map from a refined test scheme into the original cover member containing it. -/
def directedRefinementOverMap (k : (Directed.OpenRefinement.directedOpenRefinement C).I₀) :
    FamilyOpenCover.overOpenCoverObject T (Directed.OpenRefinement.directedOpenRefinement C) k ⟶ FamilyOpenCover.overOpenCoverObject T C k.1 :=
  Over.homMk (Directed.OpenRefinement.directedOpenRefinement_toMember C k)
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun a => a ≫ T.hom) (Directed.OpenRefinement.directedOpenRefinement_toMember_map C k)))

theorem directedRefinementOverMap_base (k : (Directed.OpenRefinement.directedOpenRefinement C).I₀) :
    directedRefinementOverMap T C k ≫ FamilyOpenCover.overOpenCoverMap T C k.1 =
      FamilyOpenCover.overOpenCoverMap T (Directed.OpenRefinement.directedOpenRefinement C) k := by
  apply Over.OverMorphism.ext
  exact Directed.OpenRefinement.directedOpenRefinement_toMember_map C k

/-- Matching local embedded families agree on every common test scheme over two cover members. -/
structure EmbeddedFamilyMatchingData where
  family : ∀ i, Closed.Families.FlatClosedFamily (FamilyFunctor.embeddedFamilyAmbient P (FamilyOpenCover.overOpenCoverObject T C i))
  compatible : ∀ {V : Over S} (i j : C.I₀)
    (f : V ⟶ FamilyOpenCover.overOpenCoverObject T C i) (h : V ⟶ FamilyOpenCover.overOpenCoverObject T C j),
    f ≫ FamilyOpenCover.overOpenCoverMap T C i = h ≫ FamilyOpenCover.overOpenCoverMap T C j →
      (FamilyFunctor.embeddedFlatFamilyFunctor P).map f.op (family i) =
        (FamilyFunctor.embeddedFlatFamilyFunctor P).map h.op (family j)

variable {P T C}

/-- Functoriality of restriction, expressed directly on flat families. -/
theorem embeddedFlatFamily_pullback_comp {V W Z : Over S} (f : V ⟶ W) (h : W ⟶ Z)
    (F : Closed.Families.FlatClosedFamily (FamilyFunctor.embeddedFamilyAmbient P Z)) :
    (FamilyFunctor.embeddedFlatFamilyFunctor P).map (f ≫ h).op F =
      (FamilyFunctor.embeddedFlatFamilyFunctor P).map f.op ((FamilyFunctor.embeddedFlatFamilyFunctor P).map h.op F) := by
  apply Closed.Families.FlatClosedFamily.ext
  change F.ideal.comap (FamilyFunctor.embeddedFamilyAmbientMap P (f ≫ h)) =
    (F.ideal.comap (FamilyFunctor.embeddedFamilyAmbientMap P h)).comap (FamilyFunctor.embeddedFamilyAmbientMap P f)
  rw [PullbackIdentity.embeddedFamilyAmbientMap_comp, Scheme.IdealSheafData.comap_comp]

/-- A matching family on an arbitrary cover gives compatible families on its directed refinement. -/
def EmbeddedFamilyMatchingData.refinement (D : EmbeddedFamilyMatchingData P T C) :
    FamilyDescentData.EmbeddedFamilyDescentData P T (Directed.OpenRefinement.directedOpenRefinement C) where
  family k := (FamilyFunctor.embeddedFlatFamilyFunctor P).map (directedRefinementOverMap T C k).op (D.family k.1)
  compatible {i j} f := by
    let a := CoverComparisons.overOpenCoverTransition T (Directed.OpenRefinement.directedOpenRefinement C) f
    let qᵢ := directedRefinementOverMap T C i
    let qⱼ := directedRefinementOverMap T C j
    have he : (a ≫ qⱼ) ≫ FamilyOpenCover.overOpenCoverMap T C j.1 = qᵢ ≫ FamilyOpenCover.overOpenCoverMap T C i.1 :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun b => a ≫ b) (directedRefinementOverMap_base T C j)).trans
          ((CoverComparisons.overOpenCoverTransition_map T (Directed.OpenRefinement.directedOpenRefinement C) f).trans
            (directedRefinementOverMap_base T C i).symm))
    exact (embeddedFlatFamily_pullback_comp a qⱼ (D.family j.1)).symm.trans
      (D.compatible j.1 i.1 (a ≫ qⱼ) qᵢ he)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyMatching
