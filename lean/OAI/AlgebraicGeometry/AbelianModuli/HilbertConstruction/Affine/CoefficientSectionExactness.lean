import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.QuasicoherentEpimorphisms
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Coefficient Section Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoefficientSectionExactness

noncomputable section

/-! Short exact sequences of quasicoherent sheaves remain short exact on coefficient-linear affine sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem affine_coefficient_sections_shortExact {X : Scheme.{u}} {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) {T : ShortComplex X.Modules} (hT : T.ShortExact)
    [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    (T.map (Coefficient.SectionEvaluation.coefficientSectionFunctor c U)).ShortExact := by
  have : Mono T.f := hT.mono_f
  have : Epi T.g := hT.epi_g
  let F := Coefficient.SectionEvaluation.coefficientSectionFunctor c U
  have hf : Mono (F.map T.f) := inferInstance
  have hg : Epi (F.map T.g) := by
    rw [ModuleCat.epi_iff_surjective]
    exact AffineOpen.QuasicoherentEpimorphisms.affineOpen_quasicoherent_surjective_of_epi T.g U hU
  exact ShortComplex.ShortExact.mk'
    (hT.exact.map_of_mono_of_preservesKernel F hT.mono_f inferInstance) hf hg

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoefficientSectionExactness
