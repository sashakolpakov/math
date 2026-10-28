import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Derived
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Witt Frames -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.WittFrames

noncomputable section

/-!
# Finite polynomial Witt frames for actual affine charts

Every finite-type residue algebra has a finite polynomial presentation.
Lifting its coefficient map through Witt reduction gives a surjective
smooth polynomial presentation over the Witt ring. The previously proved
frame and Čech constructions therefore apply without a supplied smooth
presentation. Affine opens in a smooth residue scheme satisfy the required
finite-type condition.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

namespace FiniteWittFrames

variable (k B : Type u) [Field k] [CommRing B] [Algebra k B]

structure Presentation where
  indices : Type u
  [finite : Fintype indices]
  map : MvPolynomial indices k →ₐ[k] B
  surjective : Function.Surjective map

attribute [instance] Presentation.finite

variable [Algebra.FiniteType k B]

theorem presentation_nonempty : Nonempty (Presentation k B) := by
  obtain ⟨ι, hι, g, hg⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial' (R := k) (S := B)).mp inferInstance
  exact ⟨{ indices := ι, finite := hι, map := g, surjective := hg }⟩

def presentation : Presentation k B := Classical.choice (presentation_nonempty k B)

abbrev Variables := (presentation k B).indices

instance variablesFintype : Fintype (Variables k B) := (presentation k B).finite

variable (p : ℕ) [Fact p.Prime] [CharP k p]

abbrev Ring := MvPolynomial (Variables k B) (WittVector p k)

instance ringSmooth : Algebra.Smooth (WittVector p k) (Ring k B p) := by
  exact ⟨inferInstance, inferInstance⟩

def reduction : Ring k B p →+* B :=
  (presentation k B).map.toRingHom.comp (MvPolynomial.map (WittVector.constantCoeff : WittVector p k →+* k))

omit [CharP k p] in
theorem reduction_surjective : Function.Surjective (reduction k B p) :=
  (presentation k B).surjective.comp
    (MvPolynomial.map_surjective WittVector.constantCoeff (WittVector.constantCoeff_surjective p))

omit [CharP k p] in
theorem reduction_base : (reduction k B p).comp (algebraMap (WittVector p k) (Ring k B p)) =
    (algebraMap k B).comp WittVector.constantCoeff := by
  ext w
  change (presentation k B).map
    (MvPolynomial.map WittVector.constantCoeff (MvPolynomial.C w)) = algebraMap k B (WittVector.constantCoeff w)
  rw [MvPolynomial.map_C]
  exact (presentation k B).map.commutes _

def frame (n : ℕ) : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B) :=
  AffineFrameCover.CrystallineAffineFrameCover.frame p k B (Ring k B p) (reduction k B p)
    (reduction_surjective k B p) (reduction_base k B p) n

/-- Every native crystalline object over Spec B maps to a constructed finite polynomial frame. -/
theorem exists_frameMap (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)) :
    ∃ n : ℕ, Nonempty (Q ⟶ frame k B p n) :=
  AffineFrameCover.CrystallineAffineFrameCover.exists_frameMap p k B Q (Ring k B p) (reduction k B p)
    (reduction_surjective k B p) (reduction_base k B p)

def resolution := CrystallineCech.Resolution.CrystallineCechResolution.complex p k B (Ring k B p) (reduction k B p)
  (reduction_surjective k B p) (reduction_base k B p)

def augmentation := CrystallineCech.Resolution.CrystallineCechResolution.augmentation p k B (Ring k B p) (reduction k B p)
  (reduction_surjective k B p) (reduction_base k B p)

instance augmentation_quasiIso : QuasiIso (augmentation k B p) :=
  CrystallineCech.Resolution.CrystallineCechResolution.augmentation_quasiIso p k B (Ring k B p) (reduction k B p)
    (reduction_surjective k B p) (reduction_base k B p)

end FiniteWittFrames

namespace CrystallineSmoothCharts

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [Smooth X.hom] (Q : Site.Object p k X)

/-- Every actual affine-open residue chart of a smooth scheme is a smooth algebra. -/
theorem residue_smooth : Algebra.Smooth k Q.residueRing := by
  have hspec : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k Q.residueRing))) := by
    rw [← Q.over_base]
    infer_instance
  have hr : RingHom.Smooth (algebraMap k Q.residueRing) := HasRingHomProperty.Spec_iff.mp hspec
  exact RingHom.smooth_algebraMap.mp hr

instance residue_finiteType : Algebra.FiniteType k Q.residueRing := by
  have := residue_smooth p k X Q
  infer_instance

/-- A finite polynomial Witt frame inside the original native crystalline site. -/
def frame (n : ℕ) : Site.Object p k X :=
  SmoothFrames.SmoothCrystallineFrames.siteFrame p k Q.residueRing (FiniteWittFrames.Ring k Q.residueRing p)
    (FiniteWittFrames.reduction k Q.residueRing p) (FiniteWittFrames.reduction_base k Q.residueRing p)
    (FiniteWittFrames.reduction_surjective k Q.residueRing p) X Q.immersion Q.over_base n

theorem exists_frameMap : ∃ n : ℕ, ∃ g : Q ⟶ frame p k X Q n, g.reducedMap = AlgHom.id k Q.residueRing :=
  SmoothFrames.SmoothCrystallineFrames.exists_siteFrameMorphism p k Q.residueRing (FiniteWittFrames.Ring k Q.residueRing p)
    (FiniteWittFrames.reduction k Q.residueRing p) (FiniteWittFrames.reduction_base k Q.residueRing p)
    (FiniteWittFrames.reduction_surjective k Q.residueRing p) X Q.immersion Q.over_base Q
    (AlgHom.id k Q.residueRing) (by change Spec.map (𝟙 _) ≫ _ = _; simp)

end CrystallineSmoothCharts

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.WittFrames
