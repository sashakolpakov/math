import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Adjunction
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Sheafification Stalk Complex -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SheafificationStalkComplex.Holomorphic

noncomputable section

/-! The actual sheafification unit is an isomorphism on complexes of module stalks. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X : TopCat.{0}}

def sheafificationStalkUnit (K : CochainComplex (X.Presheaf (ModuleCat.{0} ℂ)) ℕ) (x : X) :
    ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) x).mapHomologicalComplex (.up ℕ)).obj K ⟶
      (((TopCat.Sheaf.forget (ModuleCat.{0} ℂ) X ⋙
        TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) x).mapHomologicalComplex (.up ℕ)).obj
          (((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).mapHomologicalComplex
            (.up ℕ)).obj K)) :=
  ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) x).mapHomologicalComplex (.up ℕ)).map
    ((Complex.Adjunction.onComplexes
      (sheafificationAdjunction (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) (.up ℕ)).unit.app K)

instance sheafificationStalkUnit_isIso
    (K : CochainComplex (X.Presheaf (ModuleCat.{0} ℂ)) ℕ) (x : X) :
    IsIso (sheafificationStalkUnit K x) := by
  have h (n : ℕ) : IsIso ((sheafificationStalkUnit K x).f n) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{0} ℂ) (K.X n)
  exact HomologicalComplex.Hom.isIso_of_components _

end

end OAI.AlgebraicGeometry.Comparison.Betti.SheafificationStalkComplex.Holomorphic
