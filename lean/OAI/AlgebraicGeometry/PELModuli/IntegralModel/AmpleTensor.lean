import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PowerStability
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.BaseChange
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorSection
import OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorPowerGroup
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Ample Tensor -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleTensor.PolarizationAmpleness

noncomputable section

/-! Tensor products of ample line bundles are ample. The proof constructs
sections of an actual common tensor power and identifies their affine
nonvanishing loci, using the original HilbertConstruction definition of ampleness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorPowerGroup.Construction

universe u

variable {X : Scheme.{u}}

theorem tensorPower_class (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (n : ℕ) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower n) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L ^ n := by
  have h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower n) = Picard.Homomorphisms.LineBundleClasses.Construction.tensorPowerClass n (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) :=
    Quotient.sound ((L.tensorPower_isTensorPower n).unique (Picard.Homomorphisms.TensorPowerSheaf.Construction.tensorPowerSheaf_isTensorPower L.sheaf n))
  exact h.trans (Picard.Homomorphisms.TensorPowerGroup.Construction.tensorPowerClass_eq_pow n (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))

theorem tensor_isAmple [X.IsSeparated] {L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X}
    (hL : L.IsAmple) (hM : M.IsAmple) : (L.tensor M).IsAmple := by
  obtain ⟨hX, hLs⟩ := L.isAmple_iff_tensorPower.mp hL
  obtain ⟨_, hMs⟩ := M.isAmple_iff_tensorPower.mp hM
  refine ⟨hX, fun x => ?_⟩
  obtain ⟨n, hn, s, hxs, hs⟩ := hLs x
  obtain ⟨m, hm, t, hxt, ht⟩ := hMs x
  let L' := (L.tensorPower n).tensorPower m
  let M' := (M.tensorPower m).tensorPower n
  let P := L'.tensor M'
  have hP : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((L.tensor M).tensorPower (n * m)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((L.tensor M).tensorPower (n * m)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L' * AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M'
    simp only [L', M', tensorPower_class, ← Picard.Homomorphisms.SchemeGroup.Construction.lineBundleClass_mul, ← pow_mul, mul_pow, Nat.mul_comm m n]
  obtain ⟨e⟩ := Quotient.exact hP
  let v : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ P.sheaf :=
    Quotients.FiniteDescent.BinaryTensorId.Construction.BinaryTensorMap.tensorSection (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection s m) (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection t n)
  have hv : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing v = AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ⊓ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t := by
    exact (Quotients.FiniteDescent.TensorSection.Construction.TensorSectionLocus.nonvanishing
      (L := L') (M := M') (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection s m) (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection t n)).trans
      (congrArg₂ (fun U V : X.Opens => U ⊓ V)
        (AbelianModuli.HilbertConstruction.Section.PowerLocus.sectionNonvanishing_tensorPowerSection s m hm)
        (AbelianModuli.HilbertConstruction.Section.PowerLocus.sectionNonvanishing_tensorPowerSection t n hn))
  exact ⟨n * m, Nat.mul_pos hn hm, P,
    ((L.tensor M).tensorPower_isTensorPower (n * m)).of_targetIso e,
    v, hv.symm ▸ ⟨hxs, hxt⟩, hv.symm ▸ hs.inf ht⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleTensor.PolarizationAmpleness
