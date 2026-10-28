import OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.SupportExtension
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Support Preimage -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.SupportPreimage.BundleCycles

noncomputable section

/-! The full extended support in the punctured deformation is the actual inverse image of the original support. Flatness lifts specializations, and the constructed fiber generic point detects every point in that inverse image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X : Scheme.{0}} (I : X.IdealSheafData)

theorem puncturedExtendedSupport_coe (W : IrreducibleCloseds X) :
    (SupportExtension.BundleCycles.puncturedExtendedSupport I W : Set (Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I)) =
      DeformationCharts.BundleCycles.puncturedDeformationProjection I ⁻¹' (W : Set X) := by
  rw [SupportExtension.BundleCycles.puncturedExtendedSupport_eq_pointClosure]
  ext z
  have hW := W.isIrreducible.isGenericPoint_genericPoint W.isClosed
  change z ∈ closure {DeformationFlat.BundleCycles.puncturedFiberGenericPoint I (irreducibleSetEquivPoints W)} ↔ _
  constructor
  · intro hz
    have hs : DeformationFlat.BundleCycles.puncturedFiberGenericPoint I (irreducibleSetEquivPoints W) ⤳ z :=
      specializes_iff_mem_closure.mpr hz
    have hm := hs.map (DeformationCharts.BundleCycles.puncturedDeformationProjection I).continuous
    rw [DeformationFlat.BundleCycles.puncturedFiberGenericPoint_projection] at hm
    exact hW.specializes_iff_mem.mp hm
  · intro hz
    obtain ⟨v, hv, hp⟩ := Flat.generalizingMap (DeformationCharts.BundleCycles.puncturedDeformationProjection I) (hW.specializes hz)
    exact (DeformationFlat.BundleCycles.puncturedFiberGenericPoint_specializes I _ v hp |>.trans hv).mem_closure

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.SupportPreimage.BundleCycles
