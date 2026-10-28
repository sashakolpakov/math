import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PreservesPolarization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.CanonicalDualIsomorphisms

/-! # Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A group isomorphism preserving the graph-bundle power and ordered
level is a complete moduli isomorphism. Over a Noetherian affine base all
projective presentations used in the canonical comparison are constructed. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hδ : ∀ i, 0 < δ i)
variable (e : A.abelian.scheme ≅ B.abelian.scheme) [IsMonHom e.hom]
variable (d : ℕ) (hd : 0 < d)
variable (hgraph : Line.Bundles.LineBundle.pullbackClass e.hom.left (Line.Bundles.LineBundle.classOf B.graphBundle ^ d) =
  Line.Bundles.LineBundle.classOf A.graphBundle ^ d)
variable (hl : ∀ (T : Over S)
  (labels : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))),
  (A.level.hom.app (.op T) labels).val ≫ e.hom = (B.level.hom.app (.op T) labels).val)

def Moduli.Isomorphisms.LevelPreservingIso.ofGraphPower [IsLocallyNoetherian S]
    (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme)
    (PD : Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme) (PE : Projective.ProjectivePresentations.ProjectivePresentation B.dual.abelian.scheme) :
    Moduli.Isomorphisms.LevelPreservingIso A B :=
  Moduli.Isomorphisms.LevelPreservingIso.ofCanonicalDual A B e PB PD PE
    (A.graphPower_preserves_polarization B hδ e PB PD PE d hd hgraph) hl

def Moduli.Isomorphisms.LevelPreservingIso.ofGraphPower_noetherian_affine [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] :
    Moduli.Isomorphisms.LevelPreservingIso A B := by
  let : IsNoetherian S :=
    (isNoetherian_iff_of_finite_iSup_eq_top
      (S := fun _ : Unit => (⟨⊤, isAffineOpen_top S⟩ : S.affineOpens)) (by simp)).mpr
        (fun _ => inferInstance)
  exact Moduli.Isomorphisms.LevelPreservingIso.ofGraphPower A B hδ e d hd hgraph hl B.projectivePresentation_of_noetherian_affine
    (A.dualProjectivePresentation_of_noetherian_affine hδ)
    (B.dualProjectivePresentation_of_noetherian_affine hδ)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
