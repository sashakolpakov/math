import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.EndomorphismEquationLocus
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverOpenCoverGluing
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseGroupReflection

/-! # Automorphism Open Cover Rigidity -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismOpenCoverRigidity

noncomputable section

/-! Triviality of actual restricted polarized automorphisms is detected
by the original pullback morphisms, and hence by every open base cover. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem polarized_restriction_eq_id
    {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) {T U : Over S} (f : T ⟶ U)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback U.hom) (A.pullback U.hom))
    (h : (AutomorphismRestriction.restrictPolarizedAutomorphism A f e).abelian.hom = 𝟙 (A.abelian.pullback T.hom).scheme) :
    (Over.pullback f.left).map e.abelian.hom =
      (Over.pullback f.left).map (𝟙 (A.abelian.pullback U.hom).scheme) := by
  let c := (RosatiRestriction.polarizedRestrictionIso A f).abelian
  let F := Over.pullback f.left
  have hc : c.inv ≫ F.map e.abelian.hom ≫ c.hom = 𝟙 (A.abelian.pullback T.hom).scheme := h
  have he := congrArg (fun m => c.hom ≫ m ≫ c.inv) hc
  have hid : F.map e.abelian.hom = c.hom ≫ 𝟙 (A.abelian.pullback T.hom).scheme ≫ c.inv := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Category.id_comp,
      Iso.hom_inv_id, Category.comp_id] using he
  exact hid.trans (((congrArg (c.hom ≫ ·) (Category.id_comp c.inv)).trans c.hom_inv_id).trans
    (F.map_id _).symm)

theorem polarized_automorphism_eq_id_of_open_cover
    {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (T : Over S) (C : T.left.OpenCover)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (A.pullback T.hom))
    (h : ∀ i, (AutomorphismRestriction.restrictPolarizedAutomorphism A (OverOpenCoverGluing.OverOpenCover.inclusion T C i) e).abelian.hom =
      𝟙 (A.abelian.pullback (OverOpenCoverGluing.OverOpenCover.obj T C i).hom).scheme) :
    e.abelian.hom = 𝟙 (A.abelian.pullback T.hom).scheme :=
  Open.BaseGroupReflection.over_hom_ext_of_open_base_cover C e.abelian.hom (𝟙 _)
    (fun i => polarized_restriction_eq_id A (OverOpenCoverGluing.OverOpenCover.inclusion T C i) e (h i))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismOpenCoverRigidity
