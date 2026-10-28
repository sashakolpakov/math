import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.PushforwardComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.ZariskiComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Image
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Pushforward Zariski Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardZariskiComparison

noncomputable section

/-! An affine direct image preserves positive genuine cohomology, with its prescribed coefficient action, as computed on any ordered affine cover of a separated target. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry
universe u

theorem inverseImageOpens_iSup_eq_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type u} (U : ι → Y.Opens) (hU : ⨆ i, U i = ⊤) :
    ⨆ i, f ⁻¹ᵁ U i = ⊤ := by
  apply le_antisymm le_top
  intro x _
  have hx : f x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

def affineCover_pushforward_cohomologyIso {X Y : Scheme.{u}} [Y.IsSeparated]
    {R : Type u} [CommRing R] (f : X ⟶ Y) [IsAffineHom f]
    (c : R →+* Γ(Y, ⊤)) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens) (hU : ⨆ i, U i = ⊤)
    (haffine : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (f.appTop.hom.comp c) (n + 1)).obj M ≅
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).obj
        ((Scheme.Modules.pushforward f).obj M) := by
  letI : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have : ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent :=
    Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent f M
  exact (OrderedCech.ZariskiComparison.orderedCechZariskiModuleIso (f.appTop.hom.comp c) M (fun i ↦ f ⁻¹ᵁ U i)
    (inverseImageOpens_iSup_eq_top f U hU) (fun i ↦ (haffine i).preimage f) n).symm ≪≫
      HomologicalComplex.homologyMapIso (OrderedCech.PushforwardComplex.orderedCoefficientCechComplexPushforwardIso f c M U)
        (n + 1) ≪≫
      OrderedCech.ZariskiComparison.orderedCechZariskiModuleIso c ((Scheme.Modules.pushforward f).obj M) U hU haffine n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardZariskiComparison
