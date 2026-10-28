import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.OpenEquality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyFunctor

/-! # Family Open Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyOpenCover

noncomputable section

/-! Embedded flat families are separated with respect to open covers of the test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {S : Scheme.{u}}

/-- A member of a cover of a test scheme is itself a test scheme over the original base. -/
def overOpenCoverObject (T : Over S) (C : Scheme.OpenCover.{v} T.left) (i : C.I₀) : Over S :=
  Over.mk (C.f i ≫ T.hom)

/-- The cover morphism regarded as a morphism of test schemes. -/
def overOpenCoverMap (T : Over S) (C : Scheme.OpenCover.{v} T.left) (i : C.I₀) :
    overOpenCoverObject T C i ⟶ T := Over.homMk (C.f i) rfl

/-- Base change of a test open cover gives the corresponding open cover of its ambient family. -/
def embeddedAmbientOpenCover (P T : Over S) (C : Scheme.OpenCover.{v} T.left) :
    Scheme.OpenCover.{v} (FamilyFunctor.embeddedFamilyAmbient P T).left :=
  Scheme.Cover.copy (C.pullback₁ (FamilyFunctor.embeddedFamilyAmbient P T).hom) C.I₀
    (fun i => (FamilyFunctor.embeddedFamilyAmbient P (overOpenCoverObject T C i)).left)
    (fun i => FamilyFunctor.embeddedFamilyAmbientMap P (overOpenCoverMap T C i)) (Equiv.refl _)
    (fun i => (FamilyFunctor.embeddedFamilyAmbient_isPullback P (overOpenCoverMap T C i)).isoPullback)
    (fun i => (FamilyFunctor.embeddedFamilyAmbient_isPullback P (overOpenCoverMap T C i)).isoPullback_hom_fst.symm)

/-- Embedded flat families agreeing on an open cover of the test scheme agree globally. -/
theorem embeddedFlatFamily_eq_of_open_cover {P T : Over S}
    (C : Scheme.OpenCover.{v} T.left)
    (F G : Closed.Families.FlatClosedFamily (FamilyFunctor.embeddedFamilyAmbient P T))
    (h : ∀ i, (FamilyFunctor.embeddedFlatFamilyFunctor P).map (overOpenCoverMap T C i).op F =
      (FamilyFunctor.embeddedFlatFamilyFunctor P).map (overOpenCoverMap T C i).op G) : F = G := by
  apply Closed.Families.FlatClosedFamily.ext_on_open_cover F G (embeddedAmbientOpenCover P T C)
  intro i
  exact congrArg Closed.Families.FlatClosedFamily.ideal (h i)

/-- Equality in the embedded flat-family presheaf is local on the base. -/
theorem embeddedFlatFamily_eq_iff_on_open_cover {P T : Over S}
    (C : Scheme.OpenCover.{v} T.left)
    (F G : Closed.Families.FlatClosedFamily (FamilyFunctor.embeddedFamilyAmbient P T)) :
    F = G ↔ ∀ i, (FamilyFunctor.embeddedFlatFamilyFunctor P).map (overOpenCoverMap T C i).op F =
      (FamilyFunctor.embeddedFlatFamilyFunctor P).map (overOpenCoverMap T C i).op G :=
  ⟨fun h _ => congrArg _ h, embeddedFlatFamily_eq_of_open_cover C F G⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyOpenCover
