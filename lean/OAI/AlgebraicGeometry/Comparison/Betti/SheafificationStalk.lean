import OAI.AlgebraicGeometry.Comparison.Betti.SheafificationStalkComplex
import Mathlib.Algebra.Homology.QuasiIso

/-! # Sheafification Stalk -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SheafificationStalk.Holomorphic

noncomputable section

/-! A normalized map from sheafification has exactly the original stalk comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.HomologicalComplex

variable {X : TopCat.{0}}
  (K : CochainComplex (X.Presheaf (ModuleCat.{0} ℂ)) ℕ)
  (L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X) ℕ)

theorem sheafMap_stalk_quasiIsoAt_of_normalization
    (f : ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).mapHomologicalComplex
      (.up ℕ)).obj K ⟶ L)
    (p : K ⟶ ((TopCat.Sheaf.forget (ModuleCat.{0} ℂ) X).mapHomologicalComplex (.up ℕ)).obj L)
    (hn : (Complex.Adjunction.onComplexes
        (sheafificationAdjunction (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) (.up ℕ)).unit.app K ≫
      ((TopCat.Sheaf.forget (ModuleCat.{0} ℂ) X).mapHomologicalComplex (.up ℕ)).map f = p)
    (x : X) (n : ℕ)
    (hp : QuasiIsoAt (((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) x).mapHomologicalComplex
      (.up ℕ)).map p) n) :
    QuasiIsoAt (((TopCat.Sheaf.forget (ModuleCat.{0} ℂ) X ⋙
      TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) x).mapHomologicalComplex (.up ℕ)).map f) n := by
  let T := (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) x).mapHomologicalComplex (.up ℕ)
  have he := congrArg T.map hn
  erw [T.map_comp] at he
  change SheafificationStalkComplex.Holomorphic.sheafificationStalkUnit K x ≫
      ((TopCat.Sheaf.forget (ModuleCat.{0} ℂ) X ⋙
        TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) x).mapHomologicalComplex (.up ℕ)).map f =
      T.map p at he
  have hunit : QuasiIsoAt (SheafificationStalkComplex.Holomorphic.sheafificationStalkUnit K x) n := inferInstance
  apply (quasiIsoAt_iff_comp_left (SheafificationStalkComplex.Holomorphic.sheafificationStalkUnit K x) _ n).mp
  rw [he]
  exact hp

end

end OAI.AlgebraicGeometry.Comparison.Betti.SheafificationStalk.Holomorphic
