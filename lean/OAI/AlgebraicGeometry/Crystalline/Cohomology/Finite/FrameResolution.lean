import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.WittFrames
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Derived
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Envelope

/-! # Frame Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.FrameResolution.FiniteFrameResolution

noncomputable section

/-!
# Constructed finite frame resolutions for actual residue charts

The chosen finite polynomial Witt presentation supplies its own residue
coordinates. The native frame-coordinate resolution and its derived
comparison therefore require only finite type of the residue algebra.
Every actual affine crystalline chart of a smooth residue scheme has
such a constructed resolution.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k B : Type u) [Field k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]

def coordinates (i : WittFrames.FiniteWittFrames.Variables k B) : B :=
  (WittFrames.FiniteWittFrames.presentation k B).map (MvPolynomial.X i)

variable (p : ℕ) [Fact p.Prime] [CharP k p]

omit [CharP k p] in
theorem reduction_X (i : WittFrames.FiniteWittFrames.Variables k B) :
    WittFrames.FiniteWittFrames.reduction k B p (MvPolynomial.X i) = coordinates k B i := by
  change (WittFrames.FiniteWittFrames.presentation k B).map
    (MvPolynomial.map WittVector.constantCoeff (MvPolynomial.X i)) = _
  rw [MvPolynomial.map_X]
  rfl

def complex := CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution.complex p k B (WittFrames.FiniteWittFrames.Variables k B)
  (coordinates k B)

def augmentation := CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution.augmentation p k B (WittFrames.FiniteWittFrames.Variables k B)
  (coordinates k B)

instance augmentation_quasiIso : QuasiIso (augmentation k B p) :=
  CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution.augmentation_quasiIso p k B (WittFrames.FiniteWittFrames.Variables k B)
    (coordinates k B)

def derivedComplex := CrystallineFrame.Derived.CrystallineFrameDerived.complex p k B (WittFrames.FiniteWittFrames.Variables k B)
  (coordinates k B)

def integralCohomologyEquiv (n : ℕ) :=
  CrystallineFrame.Derived.CrystallineFrameDerived.integralCohomologyEquiv p k B (WittFrames.FiniteWittFrames.Variables k B) (coordinates k B) n

variable (X : Over (Spec (CommRingCat.of k))) [Smooth X.hom] (Q : Site.Object p k X)

def chartComplex := complex k Q.residueRing p

def chartAugmentation := augmentation k Q.residueRing p

instance chartAugmentation_quasiIso : QuasiIso (chartAugmentation k p X Q) :=
  augmentation_quasiIso k Q.residueRing p

def chartCohomologyEquiv (n : ℕ) := integralCohomologyEquiv k Q.residueRing p n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.FrameResolution.FiniteFrameResolution
