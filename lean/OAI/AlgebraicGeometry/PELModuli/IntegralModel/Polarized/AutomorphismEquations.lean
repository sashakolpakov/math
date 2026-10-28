import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualPicardAutomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.LevelRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Transport

/-! # Automorphism Equations -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismEquations

noncomputable section

/-! Polarized full-level automorphisms are specified by actual inverse,
dual-polarization, and torsion-inclusion equations. These equations will
be imposed on the bounded endomorphism parameter. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem polarizedAutomorphism_dual_eq (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A A) :
    e.dual.hom = Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback A.dual A.dual e.abelian.inv := by
  apply DualFamilyMorphism.eq_dualPicardPullback_of_poincare A.dual A.dual e.abelian.inv
  have h := congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 A.dual.abelian.scheme ⊗ₘ e.abelian.inv).left)
    e.poincare
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← Over.comp_left] at h
  simpa only [tensorHom_comp_tensorHom, Category.id_comp, Iso.inv_hom_id] using h

theorem polarizedAutomorphism_torsion_inclusion (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A A) :
    A.abelian.torsionInclusion N ≫ e.abelian.hom = A.abelian.torsionInclusion N := by
  have h := AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.torsionMap_comp_inclusion N e.abelian.hom
  rw [e.torsion_automorphism_eq_id, Category.id_comp] at h
  exact h.symm

def polarizedAutomorphismOfEquations [IsReduced S] [IsNoetherian S]
    (e : A.abelian.scheme ≅ A.abelian.scheme) [IsMonHom e.hom]
    (hpol : A.polarization.isogeny.hom ≫ Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback A.dual A.dual e.inv =
      e.hom ≫ A.polarization.isogeny.hom)
    (hlevel : A.abelian.torsionInclusion N ≫ e.hom = A.abelian.torsionInclusion N) :
    AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A A where
  abelian := e
  dual := DualPicardAutomorphism.inverseDualAutomorphism A.dual e
  abelianGroup := inferInstance
  dualGroup := inferInstance
  polarization := hpol
  poincare := DualPicardAutomorphism.inverseDualAutomorphism_poincare A.dual e
  level T c := by
    let x := A.level.hom.app (.op T) c
    let t := (A.abelian.torsionSchemePointsEquiv N T).symm x
    have ht : t ≫ A.abelian.torsionInclusion N = x.val :=
      congrArg Subtype.val ((A.abelian.torsionSchemePointsEquiv N T).apply_symm_apply x)
    change x.val ≫ e.hom = x.val
    rw [← ht, Category.assoc, hlevel]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismEquations
