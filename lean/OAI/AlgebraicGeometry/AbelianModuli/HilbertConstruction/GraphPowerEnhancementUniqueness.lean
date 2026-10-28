import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.GraphPowerEnhancementUniqueness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementTransportIso

/-! # Graph Power Enhancement Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPowerEnhancementUniqueness

noncomputable section

/-! Enhancement uniqueness is invariant under a group isomorphism to a
test of a fixed Noetherian projective family. In particular it persists
through iterated arbitrary base change of the universal family. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S T : Scheme.{u}} [IsNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : Abelian.Schemes.AbelianScheme g S) (PA : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (t : T ⟶ S)
variable (F : Level.Data.AbelianSchemeWithFullLevel g N T)
variable (e : F.abelian.scheme ≅ (A.pullback t).scheme) [IsMonHom e.hom]
variable (L : Line.Bundles.LineBundle F.abelian.scheme.left) (d : ℕ)
variable (D E : GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F L d)
variable (hδ : ∀ i, 0 < δ i) (hd : 0 < d)

def modeledGraphPowerEnhancementModuliIso : Moduli.Isomorphisms.LevelPreservingIso D.object E.object := by
  let G : Level.Data.AbelianSchemeWithFullLevel g N T := ⟨A.pullback t, F.level.transport e⟩
  let K := L.pullback e.inv.left
  have he : Line.Bundles.LineBundle.pullbackClass e.hom.left (Line.Bundles.LineBundle.classOf K) = Line.Bundles.LineBundle.classOf L :=
    (Line.Bundles.LineBundle.pullbackIso ((Over.forget T).mapIso e)).right_inv (Line.Bundles.LineBundle.classOf L)
  let D' := D.transportFamily (G := G) (M := K) e he
  let E' := E.transportFamily (G := G) (M := K) e he
  let q := Universal.GraphPowerEnhancementUniqueness.universalGraphPowerEnhancementModuliIso A PA (Over.mk t) G.level K d D' E' hδ hd
  exact (D.transportFamilyModuliIso (G := G) (M := K) e he rfl).trans
    (q.trans (E.transportFamilyModuliIso (G := G) (M := K) e he rfl).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPowerEnhancementUniqueness
