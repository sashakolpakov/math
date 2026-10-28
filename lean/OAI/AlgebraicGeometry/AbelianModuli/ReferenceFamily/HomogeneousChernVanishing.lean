import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneousLinePowers
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernClassOperations
import OAI.RepresentationTheory.Theta.Geometric.AbelianScheme
import OAI.AlgebraicGeometry.AbelianVariety.PowerCohomology

/-! # Homogeneous Chern Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneousChernVanishing

noncomputable section

/-! The original native rational Chern class of a homogeneous line
bundle vanishes. Multiplication by two scales its actual Picard class by
two and its degree-two cohomology class by four. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem lineBundleClassChernClass_one (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    Intrinsic.ChernClasses.lineBundleClassChernClass X 1 = 0 := ChernClassOperations.lineBundleChernClass_trivial X

theorem lineBundleClassChernClass_mul (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (a b : HilbertConstruction.Line.Bundles.LineBundle.IsoClass X.carrier) :
    Intrinsic.ChernClasses.lineBundleClassChernClass X (a * b) =
      Intrinsic.ChernClasses.lineBundleClassChernClass X a + Intrinsic.ChernClasses.lineBundleClassChernClass X b :=
  ChernClassOperations.lineBundleClassChernClass_tensor X a b

theorem lineBundleClassChernClass_pow (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (a : HilbertConstruction.Line.Bundles.LineBundle.IsoClass X.carrier) (n : ℕ) :
    Intrinsic.ChernClasses.lineBundleClassChernClass X (a ^ n) = n • Intrinsic.ChernClasses.lineBundleClassChernClass X a := by
  induction n with
  | zero => simp only [pow_zero, lineBundleClassChernClass_one, zero_smul]
  | succ n ih =>
    rw [pow_succ, lineBundleClassChernClass_mul, ih, succ_nsmul]

theorem homogeneousLineClass_chern_eq_zero (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (q : HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.toOver.left)
    (hq : HomogeneousLinePowers.IsHomogeneousLineClass (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety A) q) :
    Intrinsic.ChernClasses.lineBundleClassChernClass A.variety.presentation q = 0 := by
  let : IsProper A.toOver.hom := A.variety.presentation.projective.isProper
  let : CompactSpace A.toOver.left := QuasiCompact.compactSpace_of_compactSpace A.toOver.hom
  let : QuasiSeparatedSpace A.toOver.left := quasiSeparatedSpace_of_quasiSeparated A.toOver.hom
  let : CompactSpace (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety A).scheme.left :=
    inferInstanceAs (CompactSpace A.toOver.left)
  let : QuasiSeparatedSpace (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety A).scheme.left :=
    inferInstanceAs (QuasiSeparatedSpace A.toOver.left)
  have hp := HomogeneousLinePowers.homogeneousLineClass_power (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety A) q hq 2
  have hc := congrArg (Intrinsic.ChernClasses.lineBundleClassChernClass A.variety.presentation) hp
  have hc' := hc.trans (lineBundleClassChernClass_pow A.variety.presentation q 2)
  have hn := ChernClassOperations.lineBundleClassChernClass_pullback
    (X := A.variety.presentation) (Y := A.variety.presentation)
    (AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism A 2) q
  have hb := AbelianVariety.PowerCohomology.Constructions.Exterior.abelianPower_rationalBetti A 2 2
    (Intrinsic.ChernClasses.lineBundleClassChernClass A.variety.presentation q)
  have he : (4 : ℚ) • Intrinsic.ChernClasses.lineBundleClassChernClass A.variety.presentation q =
      (2 : ℚ) • Intrinsic.ChernClasses.lineBundleClassChernClass A.variety.presentation q := by
    have h := hb.symm.trans (hn.symm.trans hc')
    norm_num at h
    simpa only [← Nat.cast_smul_eq_nsmul ℚ, Nat.cast_ofNat] using h
  have hz : (2 : ℚ) • Intrinsic.ChernClasses.lineBundleClassChernClass A.variety.presentation q = 0 := by
    have h := sub_eq_zero.mpr he
    rw [← sub_smul] at h
    norm_num at h ⊢
    exact h
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

theorem homogeneousLineBundle_chern_eq_zero (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (hL : HomogeneousLinePowers.IsHomogeneousLineClass (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety A) (HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation L = 0 :=
  homogeneousLineClass_chern_eq_zero A (HilbertConstruction.Line.Bundles.LineBundle.classOf L) hL

theorem alternatingClassPairing_zero (X : TopCat.{0}) (m : TopCat.of (X × X) ⟶ X) :
    HomologyCrossPairing.alternatingClassPairing X m 0 = 0 := by
  have h := ChernClassOperations.alternatingClassPairing_add X m 0 0
  rw [zero_add] at h
  exact (add_left_cancel (a := HomologyCrossPairing.alternatingClassPairing X m 0)
    ((add_zero _).trans h)).symm

theorem homogeneousLineBundle_nativeChernForm_eq_zero (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (hL : HomogeneousLinePowers.IsHomogeneousLineClass (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety A) (HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    Intrinsic.ChernPairing.nativeChernForm A L = 0 := by
  unfold Intrinsic.ChernPairing.nativeChernForm
  rw [homogeneousLineBundle_chern_eq_zero A L hL, alternatingClassPairing_zero]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneousChernVanishing
