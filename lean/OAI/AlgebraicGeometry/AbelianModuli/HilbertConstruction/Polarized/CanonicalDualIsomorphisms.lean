import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.DualProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.DualIsomorphisms

/-! # Canonical Dual Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Over a Noetherian affine base, canonical duality completes a polarization- and level-preserving group isomorphism using projective presentations constructed from the polarized objects themselves. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
universe u

variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
variable {g N : ℕ} {δ : Fin g → ℕ} (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

def Moduli.Isomorphisms.LevelPreservingIso.ofCanonicalDual_noetherian_affine (hδ : ∀ i, 0 < δ i)
    (e : A.abelian.scheme ≅ B.abelian.scheme) [IsMonHom e.hom]
    (hp : A.polarization.isogeny.hom ≫ (A.dual.familyComparisonIso B.dual e).hom =
      e.hom ≫ B.polarization.isogeny.hom)
    (hl : ∀ (T : Over S)
      (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))),
      (A.level.hom.app (.op T) c).val ≫ e.hom = (B.level.hom.app (.op T) c).val) :
    Moduli.Isomorphisms.LevelPreservingIso A B := by
  have : IsNoetherian S :=
    (isNoetherian_iff_of_finite_iSup_eq_top
      (S := fun _ : Unit => (⟨⊤, isAffineOpen_top S⟩ : S.affineOpens)) (by simp)).mpr
        (fun _ => inferInstance)
  exact Moduli.Isomorphisms.LevelPreservingIso.ofCanonicalDual A B e B.projectivePresentation_of_noetherian_affine
    (A.dualProjectivePresentation_of_noetherian_affine hδ)
    (B.dualProjectivePresentation_of_noetherian_affine hδ) hp hl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
