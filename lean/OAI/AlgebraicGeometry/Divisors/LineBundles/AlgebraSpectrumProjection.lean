import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberGenericPoint
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Algebra Spectrum Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AlgebraSpectrumProjection.BundleCycles

noncomputable section

/-! The spectrum projection of an actual algebra, including faithful
flatness forced by flatness and its nonempty integral fibers. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]

def algebraSpectrumProjection : Spec (.of S) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))

instance algebraSpectrumProjection_flat [Module.Flat R S] : Flat (algebraSpectrumProjection R S) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

theorem algebraSpectrumProjection_faithfullyFlat [Flat (algebraSpectrumProjection R S)]
    [GeometricallyIntegral (algebraSpectrumProjection R S)] : Module.FaithfullyFlat R S :=
  RingHom.faithfullyFlat_algebraMap_iff.mp
    ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R S))).mp
      ⟨inferInstanceAs (Flat (algebraSpectrumProjection R S)),
        inferInstanceAs (Surjective (algebraSpectrumProjection R S))⟩)

theorem algebraSpectrumProjection_comap_map [Flat (algebraSpectrumProjection R S)]
    [GeometricallyIntegral (algebraSpectrumProjection R S)] (p : Ideal R) :
    Ideal.comap (algebraMap R S) (p.map (algebraMap R S)) = p := by
  let : Module.FaithfullyFlat R S := algebraSpectrumProjection_faithfullyFlat R S
  exact Ideal.comap_map_eq_self_of_faithfullyFlat p

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AlgebraSpectrumProjection.BundleCycles
