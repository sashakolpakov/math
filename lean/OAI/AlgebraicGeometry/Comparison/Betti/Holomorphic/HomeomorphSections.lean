import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ScalarSheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.ZariskiHomeomorphism

/-! # Homeomorph Sections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.HomeomorphSections.Dolbeault

noncomputable section

/-! Pullback of native holomorphic functions along a biholomorphic
homeomorphism, on every open subset and with the original restrictions. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

variable {E F M N : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]
  (e : M ≃ₜ N) (he : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ e)
  (he' : ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, E) ∞ e.symm)

def homeomorphOpenForward (U : Opens N) : e.opensCongr.symm U → U :=
  fun x => ⟨e x.val, x.property⟩

def homeomorphOpenInverse (U : Opens N) : U → e.opensCongr.symm U :=
  fun y => ⟨e.symm y.val, by
    change e (e.symm y.val) ∈ U
    simpa only [Homeomorph.apply_symm_apply] using y.property⟩

include he in
theorem homeomorphOpenForward_holomorphic (U : Opens N) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ (homeomorphOpenForward e U) := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact he.comp (contMDiff_subtype_val (U := e.opensCongr.symm U))

include he' in
theorem homeomorphOpenInverse_holomorphic (U : Opens N) :
    ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, E) ∞ (homeomorphOpenInverse e U) := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact he'.comp (contMDiff_subtype_val (U := U))

def holomorphicHomeomorphSectionEquiv (U : Opens N) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := e.opensCongr.symm U) ≃ₗ[ℂ]
      DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := F) (M := U) where
  toFun f := ⟨fun y => f (homeomorphOpenInverse e U y),
    f.contMDiff.comp (homeomorphOpenInverse_holomorphic e he' U)⟩
  invFun g := ⟨fun x => g (homeomorphOpenForward e U x),
    g.contMDiff.comp (homeomorphOpenForward_holomorphic e he U)⟩
  left_inv f := by
    apply ContMDiffMap.ext
    intro x
    change f ⟨e.symm (e x.val), _⟩ = f x
    congr 1
    exact Subtype.ext (e.symm_apply_apply x.val)
  right_inv g := by
    apply ContMDiffMap.ext
    intro y
    change g ⟨e (e.symm y.val), _⟩ = g y
    congr 1
    exact Subtype.ext (e.apply_symm_apply y.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem holomorphicHomeomorphSectionEquiv_restrict {U V : Opens N} (h : U ≤ V)
    (f : DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := e.opensCongr.symm V)) :
    holomorphicHomeomorphSectionEquiv e he he' U
        (ScalarSheaf.Dolbeault.holomorphicScalarRestrict E M (e.opensCongr.symm.monotone h) f) =
      ScalarSheaf.Dolbeault.holomorphicScalarRestrict F N h (holomorphicHomeomorphSectionEquiv e he he' V f) := rfl

def holomorphicHomeomorphSheafIso :
    (NumberTheory.PadicHodge.IntegralComparison.ZariskiHomeomorphism.sheafEquiv e (ModuleCat.{0} ℂ)).functor.obj
        (ScalarSheaf.Dolbeault.holomorphicScalarSheaf E M) ≅ ScalarSheaf.Dolbeault.holomorphicScalarSheaf F N :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun U => (holomorphicHomeomorphSectionEquiv e he he' U.unop).toModuleIso) (by
      intro U V h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact holomorphicHomeomorphSectionEquiv_restrict e he he' (leOfHom h.unop) f))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.HomeomorphSections.Dolbeault
