import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.QuotientComplex
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Quasi Iso -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.QuasiIso

noncomputable section

/-! Reduction modulo a parameter preserves a quasi-isomorphism
between complexes on whose terms the parameter is regular. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.QuotientComplex

variable (R : Type u) [CommRing R] (r : R)
  {K L : ChainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ L)

def sequenceMap : QuotientComplex.sequence R r K ⟶ QuotientComplex.sequence R r L where
  τ₁ := φ
  τ₂ := φ
  τ₃ := ((QuotientComplex.quotient R r).mapHomologicalComplex (ComplexShape.down ℕ)).map φ
  comm₁₂ := by
    change φ ≫ (r • 𝟙 L) = (r • 𝟙 K) ≫ φ
    simp
  comm₂₃ := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

theorem quasiIso (hK : ∀ i, IsSMulRegular (K.X i) r)
    (hL : ∀ i, IsSMulRegular (L.X i) r) [QuasiIso φ] :
    QuasiIso (((QuotientComplex.quotient R r).mapHomologicalComplex (ComplexShape.down ℕ)).map φ) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (sequenceMap R r φ)
    (QuotientComplex.shortExact R r K hK) (QuotientComplex.shortExact R r L hL)
    (inferInstanceAs (QuasiIso φ)) (inferInstanceAs (QuasiIso φ))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.QuasiIso
