import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Comm Group Type Map -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CommGroupTypeMap.Construction

noncomputable section

/-! Lift a natural map of underlying types using its actual pointwise
group homomorphisms and the specified natural identifications. -/

open _root_.CategoryTheory

universe u v w

def commGroupNatTransOfType {C : Type u} [Category.{v} C]
    {F G : C ⥤ CommGrpCat.{w}} {P Q : C ⥤ Type w}
    (eF : F ⋙ forget CommGrpCat ≅ P) (eG : G ⋙ forget CommGrpCat ≅ Q)
    (a : P ⟶ Q) (maps : ∀ T, F.obj T →* G.obj T)
    (hm : ∀ T x, eG.hom.app T (maps T x) = a.app T (eF.hom.app T x)) : F ⟶ G where
  app T := CommGrpCat.ofHom (maps T)
  naturality {T U} t := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply (ConcreteCategory.bijective_of_isIso (eG.hom.app U)).injective
    calc
      eG.hom.app U (maps U (F.map t x)) = a.app U (eF.hom.app U (F.map t x)) := hm U _
      _ = a.app U (P.map t (eF.hom.app T x)) := congrArg (a.app U) (eF.hom.naturality_apply t x)
      _ = Q.map t (a.app T (eF.hom.app T x)) := a.naturality_apply t _
      _ = Q.map t (eG.hom.app T (maps T x)) := congrArg (Q.map t) (hm T x).symm
      _ = eG.hom.app U (G.map t (maps T x)) := (eG.hom.naturality_apply t _).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CommGroupTypeMap.Construction
