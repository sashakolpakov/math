import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.LevelIsoFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.IsoFunctor

/-! # Level Iso Forget -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.LevelIsoForget

noncomputable section

/-! Forgetting polarization and full level is an injective natural map to the functor of underlying family isomorphisms. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

def familyLevelIsoForget : LevelIsoFunctor.familyLevelIsoFunctor A B ⟶ IsoFunctor.familyIsoFunctor A.abelian.scheme B.abelian.scheme where
  app T := TypeCat.ofHom (fun (e : Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.unop.hom)
    (B.pullback T.unop.hom)) => e.abelian)
  naturality _ _ c := by
    apply ConcreteCategory.hom_ext
    intro e
    apply Iso.ext
    exact Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint_abelian_hom A B c.unop e

theorem familyLevelIsoForget_injective (T : Over S) :
    Function.Injective ((familyLevelIsoForget A B).app (.op T)) := by
  intro e f h
  apply Moduli.Isomorphisms.LevelPreservingIso.ext_abelian
  exact congrArg Iso.hom h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.LevelIsoForget
