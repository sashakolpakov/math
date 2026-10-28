import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.QuasiProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveParameterCuts

/-! # Hilbert Parameter Geometry -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.HilbertParameterGeometry

noncomputable section

/-! The specified smooth Hilbert parameter is noetherian over a noetherian base, and its universal family is proper, flat, and finitely presented. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

instance smoothHilbertParameter_noetherian (S : Scheme.{u}) [IsNoetherian S]
    (n : ℕ) (P : Polynomial ℚ) : IsNoetherian (Parameter.smoothHilbertParameter S n P).left :=
  (QuasiProjectivity.smoothHilbertParameterQuasiProjectivePresentation S n P).noetherian

instance smoothHilbertUniversalFamily_proper (S : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) :
    IsProper (Parameter.smoothHilbertUniversalFamily S n P).family.scheme.hom :=
  (Parameter.smoothHilbertUniversalFamily S n P).family.proper

instance smoothHilbertUniversalFamily_flat (S : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) :
    Flat (Parameter.smoothHilbertUniversalFamily S n P).family.scheme.hom :=
  (Parameter.smoothHilbertUniversalFamily S n P).family.flat

instance smoothHilbertUniversalFamily_locallyFinitePresentation (S : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) :
    LocallyOfFinitePresentation (Parameter.smoothHilbertUniversalFamily S n P).family.scheme.hom :=
  (Parameter.smoothHilbertUniversalFamily S n P).family.locallyFinitePresentation

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.HilbertParameterGeometry
