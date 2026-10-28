import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CartesianBundle
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionCongr
import Mathlib.AlgebraicGeometry.Restrict

/-! # Base Changed -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseChanged

noncomputable section

/-! Transport of actual line-bundle frames along axis squares, rational
fibers, and Cartesian models of an open inverse image. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.BaseChangedBundleFrames

def axis {X Y X' Y' : Scheme.{u}} (i : Y ⟶ X) (p : X' ⟶ X) (q : Y' ⟶ Y) (j : Y' ⟶ X')
    (h : q ≫ i = j ≫ p) (M : X.Modules)
    (e : (Scheme.Modules.pullback i).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback p).obj M) ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y' :=
  (PullbackSectionCongr.Construction.PullbackSectionSquare.iso i p q j h M).symm ≪≫
    (Scheme.Modules.pullback q).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso q

def fiber {X Y S T B : Scheme.{u}} (p : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (t : T ⟶ S)
    (h : IsPullback p ρ π t) (s : B ⟶ T) (s₀ : B ⟶ S) (hs : s ≫ t = s₀) (M : X.Modules)
    (e : (Scheme.Modules.pullback (pullback.fst π s₀)).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback π s₀)) :
    (Scheme.Modules.pullback (pullback.fst ρ s)).obj ((Scheme.Modules.pullback p).obj M) ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback ρ s) := by
  have H : IsPullback (pullback.fst ρ s ≫ p) (pullback.snd ρ s) π s₀ := by
    rw [← hs]
    exact (IsPullback.of_hasPullback ρ s).paste_horiz h
  exact (Scheme.Modules.pullbackComp (pullback.fst ρ s) p).app M ≪≫
    CartesianBundle.Construction.CartesianBundleTriviality.iso (pullback.fst ρ s ≫ p) π (pullback.snd ρ s) s₀ H M e

def openFrame {X Y S : Scheme.{u}} (p : Y ⟶ X) (π : X ⟶ S) (U : S.Opens)
    (ρ : Y ⟶ U.toScheme) (h : IsPullback p ρ π U.ι) (M : X.Modules)
    (e : (Scheme.Modules.pullback p).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    (Scheme.Modules.pullback (π ⁻¹ᵁ U).ι).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π ⁻¹ᵁ U).toScheme := by
  let E : Y ≅ (π ⁻¹ᵁ U).toScheme := h.isoPullback ≪≫ pullbackRestrictIsoRestrict π U
  have hE : E.hom ≫ (π ⁻¹ᵁ U).ι = p := by
    simp only [E, Iso.trans_hom, Category.assoc, pullbackRestrictIsoRestrict_hom_ι,
      h.isoPullback_hom_fst]
  have hi : E.inv ≫ p = (π ⁻¹ᵁ U).ι := by
    apply (cancel_epi E.hom).mp
    rw [← Category.assoc, E.hom_inv_id, Category.id_comp, hE]
  exact (Scheme.Modules.pullbackCongr hi.symm).app M ≪≫
    ((Scheme.Modules.pullbackComp E.inv p).app M).symm ≪≫
    (Scheme.Modules.pullback E.inv).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso E.inv

end Construction.BaseChangedBundleFrames

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseChanged
