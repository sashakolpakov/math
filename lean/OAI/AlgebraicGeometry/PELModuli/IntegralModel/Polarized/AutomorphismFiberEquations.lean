import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismEquations
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.TorsionFixingBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RosatiBaseChange

/-! # Automorphism Fiber Equations -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismFiberEquations

noncomputable section

/-! Fixed inverse-dual and torsion equations produce the actual
polarized full-level automorphism after any base change. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S T : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (e : A.abelian.scheme ≅ A.abelian.scheme) [IsMonHom e.hom]
    (d : A.dual.abelian.scheme ≅ A.dual.abelian.scheme) [IsMonHom d.hom]
    (hP : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d.hom ⊗ₘ e.hom).left A.dual.poincare.classOf = A.dual.poincare.classOf)

local instance (f : T ⟶ S) : GrpObj ((Over.pullback f).obj A.abelian.scheme) := Functor.grpObjObj
local instance (f : T ⟶ S) : GrpObj ((Over.pullback f).obj A.dual.abelian.scheme) := Functor.grpObjObj

def polarizedAutomorphismOnFiber (f : T ⟶ S)
    (hpol : (Over.pullback f).map (A.polarization.isogeny.hom ≫ d.hom) =
      (Over.pullback f).map (e.hom ≫ A.polarization.isogeny.hom))
    (hlevel : (Over.pullback f).map (A.abelian.torsionInclusion N ≫ e.hom) =
      (Over.pullback f).map (A.abelian.torsionInclusion N)) :
    AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback f) (A.pullback f) where
  abelian := (Over.pullback f).mapIso e
  dual := (Over.pullback f).mapIso d
  abelianGroup := inferInstanceAs (IsMonHom ((Over.pullback f).map e.hom))
  dualGroup := inferInstanceAs (IsMonHom ((Over.pullback f).map d.hom))
  polarization := ((Over.pullback f).map_comp _ _).symm.trans
    (hpol.trans ((Over.pullback f).map_comp _ _))
  poincare := (AbelianModuli.ReferenceFamily.RosatiBaseChange.poincareEndomorphism_baseChange A.dual d.hom e.hom f).trans
    (congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.dual.poincarePullbackOverMap f).left) hP)
  level U c := by
    let x := (A.level.pullback f).hom.app (.op U) c
    let t := ((A.abelian.pullback f).torsionSchemePointsEquiv N U).symm x
    have ht : t ≫ (A.abelian.pullback f).torsionInclusion N = x.val :=
      congrArg Subtype.val (((A.abelian.pullback f).torsionSchemePointsEquiv N U).apply_symm_apply x)
    change x.val ≫ (Over.pullback f).map e.hom = x.val
    rw [← ht, Category.assoc, (TorsionFixingBaseChange.fixes_torsion_baseChange_iff A.abelian f N e.hom).mp hlevel]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismFiberEquations
