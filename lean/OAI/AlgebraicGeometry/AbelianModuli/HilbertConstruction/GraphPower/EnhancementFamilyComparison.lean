import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPowerEnhancementUniqueness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.IsomorphismUniqueness

/-! # Enhancement Family Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementFamilyComparison

noncomputable section

/-! A group and line compatible isomorphism has a canonical polarized
comparison between graph-power enhancements. Uniqueness fixes the
abelian component, so ordinary family cocycles imply polarized cocycles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {S T : Scheme.{u}} [IsNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}

theorem modeledGraphPowerEnhancementModuliIso_abelian
    (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (t : T ⟶ S)
    (F : Level.Data.AbelianSchemeWithFullLevel g N T)
    (e : F.abelian.scheme ≅ (A.pullback t).scheme) [IsMonHom e.hom]
    (L : Line.Bundles.LineBundle F.abelian.scheme.left) (d : ℕ)
    (D E : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F L d)
    (hδ : ∀ i, 0 < δ i) (hd : 0 < d) :
    (GraphPowerEnhancementUniqueness.modeledGraphPowerEnhancementModuliIso A P t F e L d D E hδ hd).abelian = Iso.refl F.abelian.scheme := by
  apply Iso.ext
  change e.hom ≫ (𝟙 (A.pullback t).scheme ≫ e.inv) = 𝟙 F.abelian.scheme
  rw [Category.id_comp, e.hom_inv_id]

namespace GraphPowerEnhancementFamilyComparison
variable (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (t : T ⟶ S)
    (F G : Level.Data.AbelianSchemeWithFullLevel g N T)
    (model : G.abelian.scheme ≅ (A.pullback t).scheme) [IsMonHom model.hom]
    (L : Line.Bundles.LineBundle F.abelian.scheme.left) (M : Line.Bundles.LineBundle G.abelian.scheme.left) (d : ℕ)
    (e : F.abelian.scheme ≅ G.abelian.scheme) [IsMonHom e.hom]
    (hline : Line.Bundles.LineBundle.pullbackClass e.hom.left (Line.Bundles.LineBundle.classOf M) = Line.Bundles.LineBundle.classOf L)
    (hlevel : F.level.transport e = G.level)
    (D : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F L d)
    (E : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ G M d)
    (hδ : ∀ i, 0 < δ i) (hd : 0 < d)

def iso : Moduli.Isomorphisms.LevelPreservingIso D.object E.object :=
  (D.transportFamilyModuliIso (G := G) (M := M) e hline hlevel).trans
    (GraphPowerEnhancementUniqueness.modeledGraphPowerEnhancementModuliIso A P t G model M d
      (D.transportFamily (G := G) (M := M) e hline) E hδ hd)

theorem iso_abelian :
    (iso A P t F G model L M d e hline hlevel D E hδ hd).abelian = e := by
  apply Iso.ext
  change e.hom ≫
    (GraphPowerEnhancementUniqueness.modeledGraphPowerEnhancementModuliIso A P t G model M d
      (D.transportFamily (G := G) (M := M) e hline) E hδ hd).abelian.hom = e.hom
  rw [modeledGraphPowerEnhancementModuliIso_abelian]
  exact Category.comp_id _

theorem iso_unique (q : Moduli.Isomorphisms.LevelPreservingIso D.object E.object) (hq : q.abelian = e) :
    q = iso A P t F G model L M d e hline hlevel D E hδ hd :=
  Moduli.Isomorphisms.LevelPreservingIso.ext_abelian q _
    (congrArg Iso.hom (hq.trans (iso_abelian A P t F G model L M d e hline hlevel D E hδ hd).symm))

end GraphPowerEnhancementFamilyComparison

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementFamilyComparison
