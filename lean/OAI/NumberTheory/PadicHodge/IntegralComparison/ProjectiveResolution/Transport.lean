import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-! # Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Transport

noncomputable section

/-! Transporting a projective resolution along an isomorphism of its
resolved object leaves its complex and differentials unchanged. -/

open _root_.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  {M N : C} (P : ProjectiveResolution M) (e : M ≅ N)

def alongIso : ProjectiveResolution N where
  complex := P.complex
  projective n := P.projective n
  π := P.π ≫ (ChainComplex.single₀ C).map e.hom
  quasiIso := quasiIso_comp _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Transport
