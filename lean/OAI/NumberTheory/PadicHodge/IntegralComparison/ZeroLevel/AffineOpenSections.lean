import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.SectionRestriction
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Affine Open Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.AffineOpenSections

noncomputable section

/-! Values of original level-zero crystalline sections on canonical affine opens respect restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

abbrev sectionRing (U : X.left.Opens) : CommAlgCat.{u} k :=
  (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op U)

abbrev Sections := BoundedCrystalline.CrystallineSections.Sections (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k X) 0

def frame (U : X.left.Opens) (hU : IsAffineOpen U) :=
  OpenFrame.boundedFrame p k (sectionRing k X U) X hU.fromSpec
    (AffineOpen.SectionBase.overBase k X U hU)

def value (s : Sections p k X) (U : X.left.Opens) (hU : IsAffineOpen U) : Γ(X.left, U) :=
  BoundedCrystalline.CrystallineSections.value (Witt.Crystalline.wittStructureMap p k X) 0 s (frame p k X U hU)

theorem restriction (s : Sections p k X) {U V : X.left.Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    X.left.presheaf.map (homOfLE h).op (value p k X s U hU) = value p k X s V hV := by
  let β : frame p k X V hV ⟶ frame p k X U hU :=
    Zero.FrameChartMap.boundedMap k (sectionRing k X U) (sectionRing k X V)
      (AffineOpen.SectionRestriction.algHom k X h) p X hU.fromSpec hV.fromSpec
      (AffineOpen.SectionBase.overBase k X U hU) (AffineOpen.SectionBase.overBase k X V hV)
      (AffineOpen.SectionRestriction.factorization k X h hU hV)
  exact BoundedCrystalline.CrystallineSections.value_natural
    (Witt.Crystalline.wittStructureMap p k X) 0 s β

theorem value_add (s t : Sections p k X) (U : X.left.Opens) (hU : IsAffineOpen U) :
    value p k X (s + t) U hU = value p k X s U hU + value p k X t U hU := rfl

theorem value_smul (w : Crystalline.ExactRestriction.Coeff (B := WittVector p k))
    (s : Sections p k X) (U : X.left.Opens) (hU : IsAffineOpen U) :
    value p k X (w • s) U hU =
      OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap k X U (WittVector.constantCoeff w.down) * value p k X s U hU := rfl

omit p [Fact p.Prime] [CharP k p] in
theorem smooth [Smooth X.hom] (U : X.left.Opens) (hU : IsAffineOpen U) :
    Algebra.Smooth k (sectionRing k X U) := by
  have h : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (sectionRing k X U)))) := by
    have hs : Smooth (hU.fromSpec ≫ X.hom) := inferInstance
    exact AffineOpen.SectionBase.overBase k X U hU ▸ hs
  exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp h)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.AffineOpenSections
