import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyOpenCover

/-! # Family Cover Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyCoverEquality

noncomputable section

/-! Equality of embedded families for open covers presented by arbitrary test-scheme maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {S : Scheme.{u}} {P T : Over S} {ι : Type v}

/-- Any jointly covering family of open test-scheme maps gives a cover of the test ambient. -/
def embeddedAmbientCoverOfMaps (V : ι → Over S) (f : ∀ i, V i ⟶ T)
    [∀ i, IsOpenImmersion (f i).left]
    (hc : ∀ x : T.left, ∃ i y, (f i).left y = x) :
    Scheme.OpenCover.{v} (FamilyFunctor.embeddedFamilyAmbient P T).left := by
  let C : T.left.OpenCover := Scheme.Cover.mkOfCovers ι (fun i => (V i).left)
    (fun i => (f i).left) hc
  exact Scheme.Cover.copy (C.pullback₁ (FamilyFunctor.embeddedFamilyAmbient P T).hom) ι
    (fun i => (FamilyFunctor.embeddedFamilyAmbient P (V i)).left)
    (fun i => FamilyFunctor.embeddedFamilyAmbientMap P (f i)) (Equiv.refl _)
    (fun i => (FamilyFunctor.embeddedFamilyAmbient_isPullback P (f i)).isoPullback)
    (fun i => (FamilyFunctor.embeddedFamilyAmbient_isPullback P (f i)).isoPullback_hom_fst.symm)

/-- Agreement over any open covering family of test-scheme maps implies global agreement. -/
theorem embeddedFlatFamily_eq_of_covering_maps (V : ι → Over S) (f : ∀ i, V i ⟶ T)
    [∀ i, IsOpenImmersion (f i).left]
    (hc : ∀ x : T.left, ∃ i y, (f i).left y = x)
    (F G : Closed.Families.FlatClosedFamily (FamilyFunctor.embeddedFamilyAmbient P T))
    (h : ∀ i, (FamilyFunctor.embeddedFlatFamilyFunctor P).map (f i).op F =
      (FamilyFunctor.embeddedFlatFamilyFunctor P).map (f i).op G) : F = G := by
  apply F.ext_on_open_cover G (embeddedAmbientCoverOfMaps V f hc)
  intro i
  exact congrArg Closed.Families.FlatClosedFamily.ideal (h i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyCoverEquality
