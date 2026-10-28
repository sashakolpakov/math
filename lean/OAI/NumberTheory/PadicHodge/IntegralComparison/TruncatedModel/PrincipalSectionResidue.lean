import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFractionGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedSection

/-! # Principal Section Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSectionResidue

noncomputable section

/-! A principal fraction supported outside an actual section gives
its original section residue, independently of the cover witnesses. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))
  (g : ℕ) [SmoothOfRelativeDimension g X.hom]

abbrev Below (a : Fin g → Γ(X.left,U.val)) (O : X.left.Opens) : Prop :=
  ∀ j : ULift.{0} (Fin g), (PrincipalFractionGlobal.opens p k n X U).obj
    (PrincipalFractionGlobal.family p k n X U g a j) ≤ O

abbrev Cover (a : Fin g → Γ(X.left,U.val)) (O : X.left.Opens) : Prop :=
  (PrincipalFractionGlobal.opens p k n X U).obj
    (⊤_ (PrincipalFrame.Index X.left U)) ⊓ O ≤
      ⨆ j : ULift.{0} (Fin g), (PrincipalFractionGlobal.opens p k n X U).obj
        (PrincipalFractionGlobal.family p k n X U g a j)

abbrev Global (O : X.left.Opens) : Prop :=
  (PrincipalFractionGlobal.opens p k n X U).obj
    (⊤_ (PrincipalFrame.Index X.left U)) ⊔ O = ⊤

variable (s : Spec (CommRingCat.of (Truncated.Witt.Ring p k n)) ⟶ X.left)
  [IsClosedImmersion s] (b : Fin g → Γ(X.left,U.val))
  (hb : Ideal.span (Set.range b) = s.ker.ideal U) (hs : ⊤ ≤ s ⁻¹ᵁ U.val)

abbrev sectionResidue := SupportedResidue.residue p k n X Y f hp U I g b
  (SupportedSection.punctured p k n X Y f s)
  (SupportedSection.below p k n X Y f U s g b hb)
  (SupportedSection.cover p k n X Y f U s g b hb)
  (SupportedRows.exactAt_succ p k n X Y f U I g b)
  (SupportedSection.global p k n X Y f U s hs)

variable (a : Fin g → Γ(X.left,U.val)) (hab : a = b)
  (hO : Below p k n X U g a (SectionIdealPuncturedCover.outside s.ker))
  (hcover : Cover p k n X U g a (SectionIdealPuncturedCover.outside s.ker))
  (hglobal : Global p k n X U (SectionIdealPuncturedCover.outside s.ker))

include hab in
omit [SmoothOfRelativeDimension g X.hom] in
theorem comparison :
    PrincipalFractionGlobal.boundedResidue p k n X Y f hp U I g a
      (SectionIdealPuncturedCover.outside s.ker) hO hcover hglobal =
    sectionResidue p k n X Y f hp U I g s b hb hs := by
  apply SupportedResidue.Congruence.congr p k n X Y f hp U I g
  · exact hab
  · rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSectionResidue
