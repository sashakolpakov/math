import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EqualDimensionEtaleAlgebras
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.StandardSmooth

/-! # Dimension Etale Ring Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DimensionEtaleRingMaps

noncomputable section

/-! The equal-dimension etale criterion in ring-homomorphism form. -/

universe u v w

theorem ringHom_etale_of_standardSmooth_equal_dimension
    {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (d : ℕ)
    (hf : f.IsStandardSmoothOfRelativeDimension d)
    (hgf : (g.comp f).IsStandardSmoothOfRelativeDimension d)
    (hg : g.FormallyUnramified) : g.Etale := by
  algebraize [f, g, g.comp f]
  exact EqualDimensionEtaleAlgebras.etale_of_standardSmooth_equal_dimension R S T d

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DimensionEtaleRingMaps
