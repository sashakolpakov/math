import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ImmersionIdealEmbedding
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Kernel Flat Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.KernelFlatBaseChange

noncomputable section

/-! The kernel ideal of a quasi-compact morphism commutes with flat
base change, by factoring through its scheme-theoretic image. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y S : Scheme.{u}}

theorem toImage_schemeTheoreticallyDominant (g : Y ⟶ S) :
    IsSchemeTheoreticallyDominant g.toImage := by
  constructor
  apply Closed.ImmersionIdealEmbedding.ideal_map_closed_injective g.imageι
  dsimp only
  rw [Scheme.IdealSheafData.map_ker, g.toImage_imageι,
    Scheme.IdealSheafData.map_bot, g.ker.ker_subschemeι]

theorem kernel_flat_baseChange (f : X ⟶ S) (g : Y ⟶ S)
    [Flat f] [QuasiCompact g] :
    (pullback.fst f g).ker = g.ker.comap f := by
  let : IsSchemeTheoreticallyDominant g.toImage := toImage_schemeTheoreticallyDominant g
  let e := pullbackLeftPullbackSndIso f g.imageι g.toImage
  have hz : (pullback.fst (pullback.snd f g.imageι) g.toImage).ker = ⊥ :=
    Scheme.Hom.ker_eq_bot _
  calc
    (pullback.fst f g).ker = (pullback.fst f (g.toImage ≫ g.imageι)).ker := by
      rw [g.toImage_imageι]
    _ = (e.hom ≫ pullback.fst f (g.toImage ≫ g.imageι)).ker :=
      (Scheme.Hom.ker_comp_of_isIso e.hom _).symm
    _ = (pullback.fst (pullback.snd f g.imageι) g.toImage ≫
        pullback.fst f g.imageι).ker := by
      rw [pullbackLeftPullbackSndIso_hom_fst]
    _ = g.ker.comap f := by
      rw [Scheme.Hom.ker_comp, hz, Scheme.IdealSheafData.map_bot,
        Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, g.ker.ker_subschemeι]

theorem ideal_vanishing_flat_baseChange (f : X ⟶ S) (g : Y ⟶ S)
    [Flat f] [QuasiCompact g] (K : X.IdealSheafData) :
    K.comap (pullback.fst f g) = ⊥ ↔ K ≤ g.ker.comap f := by
  rw [← le_bot_iff, ← Scheme.IdealSheafData.le_map_iff_comap_le,
    Scheme.IdealSheafData.map_bot, kernel_flat_baseChange]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.KernelFlatBaseChange
