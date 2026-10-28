import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.FormTransport

/-! # Closed Quotient Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ClosedQuotientRestriction

noncomputable section

/-! The actual ideal-quotient restriction maps agree with restriction
of regular functions on the closed subscheme, over the original base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace

open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsClosedImmersion f.left]
  (U V : Y.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (i : V ⟶ U)

def map :
    CommAlgCat.of R (SmoothClosedSections.ring R Y U ⧸ f.left.ker.ideal ⟨U, hU⟩) ⟶
      CommAlgCat.of R (SmoothClosedSections.ring R Y V ⧸ f.left.ker.ideal ⟨V, hV⟩) :=
  CommAlgCat.ofHom (Ideal.quotientMapₐ (f.left.ker.ideal ⟨V, hV⟩)
    ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R Y).map i.op).hom
    (f.left.ker.ideal_le_comap_ideal (U := ⟨V, hV⟩) (V := ⟨U, hU⟩) i.le))

omit [IsClosedImmersion f.left] in
@[simp]
theorem map_mk (a : SmoothClosedSections.ring R Y U) :
    ClosedQuotientRestriction.map R X Y f U V hU hV i (Ideal.Quotient.mk (f.left.ker.ideal ⟨U, hU⟩) a) =
      Ideal.Quotient.mk (f.left.ker.ideal ⟨V, hV⟩) (Y.left.presheaf.map i.op a) := rfl

@[reassoc]
theorem square :
    (CommAlgCat.isoMk (SmoothClosedSections.quotientEquiv R X Y f U hU)).hom ≫
      (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map ((Opens.map f.left.base).map i).op =
    ClosedQuotientRestriction.map R X Y f U V hU hV i ≫ (CommAlgCat.isoMk (SmoothClosedSections.quotientEquiv R X Y f V hV)).hom := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact (ConcreteCategory.congr_hom (f.left.naturality i.op) a).symm

theorem forms (n : ℕ)
    (ω : AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.Forms (CommAlgCat.of R (SmoothClosedSections.ring R Y U ⧸ f.left.ker.ideal ⟨U, hU⟩)) n) :
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap
        ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map ((Opens.map f.left.base).map i).op) n
      (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (CommAlgCat.isoMk (SmoothClosedSections.quotientEquiv R X Y f U hU)).hom n ω) =
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (CommAlgCat.isoMk (SmoothClosedSections.quotientEquiv R X Y f V hV)).hom n
      (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (ClosedQuotientRestriction.map R X Y f U V hU hV i) n ω) := by
  exact Exterior.FormTransport.naturality
    (CommAlgCat.isoMk (SmoothClosedSections.quotientEquiv R X Y f U hU))
    (CommAlgCat.isoMk (SmoothClosedSections.quotientEquiv R X Y f V hV))
    (ClosedQuotientRestriction.map R X Y f U V hU hV i)
    ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map ((Opens.map f.left.base).map i).op)
    (square R X Y f U V hU hV i) n ω

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ClosedQuotientRestriction
