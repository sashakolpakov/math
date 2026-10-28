import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles

/-! # Section Normalized Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SectionNormalizedTransport

noncomputable section

/-! Normalize a global transport isomorphism along a section, without trivializing the original line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (p : X ⟶ Y) (z : Y ⟶ X) (hz : z ≫ p = 𝟙 Y)
  (L : Y.Modules) (N : X.Modules)

/-- The canonical identification of a pulled-back module on the section. -/
def sourceIso : (Scheme.Modules.pullback z).obj ((Scheme.Modules.pullback p).obj L) ≅ L :=
  (Scheme.Modules.pullbackComp z p ≪≫ Scheme.Modules.pullbackCongr hz ≪≫ Scheme.Modules.pullbackId Y).app L

variable (t : (Scheme.Modules.pullback p).obj L ≅ N) (e : (Scheme.Modules.pullback z).obj N ≅ L)

/-- The actual automorphism of the original module measured on the section. -/
def discrepancy : L ≅ L :=
  (sourceIso p z hz L).symm ≪≫ (Scheme.Modules.pullback z).mapIso t ≪≫ e

/-- Correct transport by pulling back the inverse discrepancy. -/
def normalized : (Scheme.Modules.pullback p).obj L ≅ N :=
  (Scheme.Modules.pullback p).mapIso (discrepancy p z hz L N t e).symm ≪≫ t

/-- The corrected isomorphism has exactly the prescribed restriction along the section. -/
theorem normalized_section :
    (Scheme.Modules.pullback z).map (normalized p z hz L N t e).hom ≫ e.hom =
      (sourceIso p z hz L).hom := by
  let d := discrepancy p z hz L N t e
  have hd : (Scheme.Modules.pullback z).map t.hom ≫ e.hom =
      (sourceIso p z hz L).hom ≫ d.hom := by
    dsimp only [d, discrepancy]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.hom_inv_id_assoc]
  have hn : (Scheme.Modules.pullback z).map ((Scheme.Modules.pullback p).map d.inv) ≫
      (sourceIso p z hz L).hom = (sourceIso p z hz L).hom ≫ d.inv :=
    (Scheme.Modules.pullbackComp z p ≪≫ Scheme.Modules.pullbackCongr hz ≪≫
      Scheme.Modules.pullbackId Y).hom.naturality d.inv
  change (Scheme.Modules.pullback z).map ((Scheme.Modules.pullback p).map d.inv ≫ t.hom) ≫ e.hom = _
  rw [Functor.map_comp, Category.assoc, hd, ← Category.assoc, hn, Category.assoc,
    d.inv_hom_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SectionNormalizedTransport
