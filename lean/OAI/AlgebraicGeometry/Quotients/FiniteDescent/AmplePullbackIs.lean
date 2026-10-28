import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullback
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionBase
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Ample Pullback Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AmplePullbackIs.Construction.AmplePullback

noncomputable section

/-! An affine morphism pulls back an ample line bundle to an ample line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem isAmple {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (hL : L.IsAmple) : (L.pullback f).IsAmple := by
  have : CompactSpace Y := ⟨hL.1⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  apply (L.pullback f).isAmple_iff_tensorPower.mpr
  refine ⟨isCompact_univ, fun x => ?_⟩
  obtain ⟨n, hn, s, hx, hs⟩ := (L.isAmple_iff_tensorPower.mp hL).2 (f x)
  let e := TensorPullback.Construction.TensorPullbackMap.iso f L n
  let t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ ((L.pullback f).tensorPower n).sheaf :=
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s ≫ e.hom
  have ht : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t = f ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s :=
    (AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) e).trans
      (SectionBase.Construction.SectionBaseChange.nonvanishing_pullback f (L.tensorPower n) s)
  exact ⟨n, hn, t, ht.symm ▸ hx, ht.symm ▸ hs.preimage f⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AmplePullbackIs.Construction.AmplePullback
