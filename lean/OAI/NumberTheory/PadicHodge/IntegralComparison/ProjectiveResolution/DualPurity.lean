import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ProjectiveResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DualCohomology

/-! # Dual Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.DualPurity

noncomputable section

/-! Every genuine projective resolution of a regular-sequence quotient
has the same ordinary dual purity as its Koszul resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable (R : Type u) [CommRing R]

abbrev shape := NonpositiveProjectiveResolution.shape
abbrev quotient (rs : List R) := RegularSequenceKoszul.quotient (ModuleCat.of R R) rs
abbrev ordinary (rs : List R) := Koszul.DualCohomology.ordinary R rs
abbrev koszul (rs : List R) (hreg : RingTheory.Sequence.IsWeaklyRegular R rs) :=
  Koszul.ProjectiveResolution.resolution (ModuleCat.of R R) rs hreg

instance ordinary_supported (rs : List R) : (ordinary R rs).IsStrictlySupported shape.op := by
  change (((ExactModuleDualFunctor.functor R).mapHomologicalComplex (ComplexShape.up ℤ).symm).obj
    (RegularSequenceKoszul.complex (ModuleCat.of R R) rs).op).IsStrictlySupported shape.op
  infer_instance

def restrictionIso (rs : List R) (hreg : RingTheory.Sequence.IsWeaklyRegular R rs) :
    DualComplexHomology.complex R (koszul R rs hreg).complex ≅
      (ordinary R rs).restriction shape.op :=
  Hom.isoOfComponents (fun _ => Iso.refl _) (by intros; rfl)

def koszulHomologyIso (rs : List R) (hreg : RingTheory.Sequence.IsWeaklyRegular R rs) (n : ℕ) :
    (DualComplexHomology.complex R (koszul R rs hreg).complex).homology n ≅
      (ordinary R rs).homology (-(n : ℤ)) := by
  simpa only [shape, NonpositiveProjectiveResolution.shape, ComplexShape.Embedding.op_f,
    ComplexShape.embeddingUpIntLE_f, zero_sub] using
    (homologyMapIso (restrictionIso R rs hreg) n ≪≫
      Supported.SupportedRestriction.homologyIso shape.op (ordinary R rs) n)

variable (rs : List R) (hreg : RingTheory.Sequence.IsWeaklyRegular R rs)
  (P : ProjectiveResolution (quotient R rs))

def homologyIso : (DualComplexHomology.complex R P.complex).homology rs.length ≅ quotient R rs :=
  IntegralComparison.ProjectiveResolution.Hom.Comparison.homologyIso (ExactModuleDualFunctor.functor R)
    P (koszul R rs hreg) rs.length ≪≫
      koszulHomologyIso R rs hreg rs.length ≪≫ Koszul.DualCohomology.homologyIso R rs hreg

include hreg in
theorem exactAt (n : ℕ) (hn : n ≠ rs.length) :
    (DualComplexHomology.complex R P.complex).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  let e := IntegralComparison.ProjectiveResolution.Hom.Comparison.homologyIso (ExactModuleDualFunctor.functor R)
    P (koszul R rs hreg) n ≪≫ koszulHomologyIso R rs hreg n
  exact e.isZero_iff.mpr ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (Koszul.DualCohomology.exactAt R rs hreg (-(n : ℤ)) (by omega)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.DualPurity
