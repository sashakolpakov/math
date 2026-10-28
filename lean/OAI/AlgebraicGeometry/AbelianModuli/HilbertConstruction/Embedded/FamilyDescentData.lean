import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.CoverComparisons
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.AmbientTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.Gluing

/-! # Family Descent Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyDescentData

noncomputable section

/-! Compatible embedded flat families on a directed base cover give effective ideal descent data. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (P T : Over S) (C : T.left.OpenCover)
variable [Category C.I₀] [C.LocallyDirected]

/-- Local embedded families agreeing under all transitions of a directed base cover. -/
structure EmbeddedFamilyDescentData where
  family : ∀ i, Closed.Families.FlatClosedFamily (FamilyFunctor.embeddedFamilyAmbient P (FamilyOpenCover.overOpenCoverObject T C i))
  compatible : ∀ {i j} (f : i ⟶ j),
    (FamilyFunctor.embeddedFlatFamilyFunctor P).map (CoverComparisons.overOpenCoverTransition T C f).op (family j) = family i

namespace EmbeddedFamilyDescentData

variable {P T C} (D : EmbeddedFamilyDescentData P T C)

/-- Transfer each local ideal family onto the ordinary pullback ambient. -/
def canonicalFamily (i : C.I₀) : Closed.Families.FlatClosedFamily (CoverComparisons.coverPullbackAmbient P T C i) :=
  (D.family i).changeAmbient (CoverComparisons.embeddedCoverIso P T C i)

/-- The transferred ideals agree on the actual transitions of the pullback cover. -/
def idealDescentData : IdealDescent.IdealDescentData (C.pullback₁ (FamilyFunctor.embeddedFamilyAmbient P T).hom) where
  ideal i := (D.canonicalFamily i).ideal
  compatible {i j} f := by
    let eᵢ := (CoverComparisons.embeddedCoverIso P T C i).inv.left
    let eⱼ := (CoverComparisons.embeddedCoverIso P T C j).inv.left
    let a := FamilyFunctor.embeddedFamilyAmbientMap P (CoverComparisons.overOpenCoverTransition T C f)
    let d := Scheme.Cover.trans (C.pullback₁ (FamilyFunctor.embeddedFamilyAmbient P T).hom) f
    have he : eᵢ ≫ a = d ≫ eⱼ := CoverComparisons.embeddedCoverIso_inv_transition P T C f
    have hc : (D.family j).ideal.comap a = (D.family i).ideal :=
      congrArg Closed.Families.FlatClosedFamily.ideal (D.compatible f)
    change ((D.family j).ideal.comap eⱼ).comap d = (D.family i).ideal.comap eᵢ
    exact ((D.family j).ideal.comap_comp d eⱼ).symm.trans
      ((congrArg (fun p => (D.family j).ideal.comap p) he.symm).trans
        (((D.family j).ideal.comap_comp eᵢ a).trans
          (congrArg (fun I => I.comap eᵢ) hc)))

/-- The local structure map to the entire base is its structure map to the cover member followed
by the open immersion into the base. -/
theorem canonicalFamily_structure (i : C.I₀) :
    (D.idealDescentData.ideal i).subschemeι ≫
      (C.pullback₁ (FamilyFunctor.embeddedFamilyAmbient P T).hom).f i ≫ (FamilyFunctor.embeddedFamilyAmbient P T).hom =
      (D.canonicalFamily i).scheme.hom ≫ C.f i := by
  change (D.canonicalFamily i).ideal.subschemeι ≫
    pullback.fst (FamilyFunctor.embeddedFamilyAmbient P T).hom (C.f i) ≫ (FamilyFunctor.embeddedFamilyAmbient P T).hom =
    ((D.canonicalFamily i).ideal.subschemeι ≫ pullback.snd (FamilyFunctor.embeddedFamilyAmbient P T).hom (C.f i)) ≫ C.f i
  exact (congrArg (fun p => (D.canonicalFamily i).ideal.subschemeι ≫ p)
    (pullback.condition (f := (FamilyFunctor.embeddedFamilyAmbient P T).hom) (g := C.f i))).trans
      (Category.assoc _ _ _).symm

theorem canonicalFamily_flat (i : C.I₀) :
    Flat ((D.idealDescentData.ideal i).subschemeι ≫
      (C.pullback₁ (FamilyFunctor.embeddedFamilyAmbient P T).hom).f i ≫ (FamilyFunctor.embeddedFamilyAmbient P T).hom) := by
  have : Flat (D.canonicalFamily i).scheme.hom := (D.canonicalFamily i).flat
  exact (D.canonicalFamily_structure i).symm ▸
    (inferInstance : Flat ((D.canonicalFamily i).scheme.hom ≫ C.f i))

theorem canonicalFamily_locallyFinitePresentation (i : C.I₀) :
    LocallyOfFinitePresentation ((D.idealDescentData.ideal i).subschemeι ≫
      (C.pullback₁ (FamilyFunctor.embeddedFamilyAmbient P T).hom).f i ≫ (FamilyFunctor.embeddedFamilyAmbient P T).hom) := by
  have : LocallyOfFinitePresentation (D.canonicalFamily i).scheme.hom :=
    (D.canonicalFamily i).locallyFinitePresentation
  exact (D.canonicalFamily_structure i).symm ▸
    (inferInstance : LocallyOfFinitePresentation ((D.canonicalFamily i).scheme.hom ≫ C.f i))

end EmbeddedFamilyDescentData

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyDescentData
