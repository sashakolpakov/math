import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AffineLocalization
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Map

/-! # Localization -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Localization.CrystallineFrameLocalization

noncomputable section

/-!
# Localization of the native crystalline frame maps

If a native crystalline morphism localizes its ambient coefficient ring,
the actual induced frame map is the corresponding localization. This
includes the affine coordinate translations caused by choosing different
lifts on the two crystalline objects.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)
  {Q P : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)}

theorem ambientMap_isLocalization (f : Q ⟶ P) (M : Submonoid P.thickening.ring)
    (hf : M.IsLocalizationMap f.ambientMap) :
    (Algebra.algebraMapSubmonoid
      (DividedPowerAlgebra P.thickening.ring (σ →₀ P.thickening.ring)) M).IsLocalizationMap
      (Map.CrystallineFrameMap.ambientMap a f) := by
  let : Algebra P.thickening.ring Q.thickening.ring := f.ambientMap.toRingHom.toAlgebra
  have : IsLocalization M Q.thickening.ring := ⟨hf⟩
  exact Divided.AffineLocalization.DividedAffineLocalization.isLocalizationMap P.thickening.ring Q.thickening.ring σ
    (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers
    (Lifts.CrystallineFrameLifts.translation a f) (Lifts.CrystallineFrameLifts.translation_mem a f)
    (RingHom.ker P.thickening.reduction) P.thickening.dividedPowers f.dp_comp M

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Localization.CrystallineFrameLocalization
