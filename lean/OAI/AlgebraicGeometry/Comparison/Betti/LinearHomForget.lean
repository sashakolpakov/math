import OAI.AlgebraicGeometry.Comparison.Betti.IntegerAcyclicHomComplex
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Linear.Yoneda

/-! # Linear Hom Forget -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext

noncomputable section

/-! The scalar action on ordinary Hom cohomology is induced by actual scalar chain maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  {R : Type v} [CommRing R] [Linear R C] (A : C) (K : CochainComplex C ℤ)

def integerLinearHomComplex : CochainComplex (ModuleCat.{v} R) ℤ :=
  (((linearCoyoneda R C).obj (op A)).mapHomologicalComplex (.up ℤ)).obj K

def integerLinearHomologyForgetEquiv (n : ℤ) :
    (integerLinearHomComplex (R := R) A K).homology n ≃+
      (IntegerAcyclicHomComplex.Ext.integerHomComplex A K).homology n :=
  ((integerLinearHomComplex (R := R) A K).sc n).mapHomologyIso
    (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) |>.symm.addCommGroupIsoToAddEquiv

theorem integerHom_scalar_map (r : R) :
    ((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).map (r • 𝟙 K) =
      ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).mapHomologicalComplex (.up ℤ)).map
        (r • 𝟙 (integerLinearHomComplex (R := R) A K)) := by
  ext n z
  change A ⟶ K.X n at z
  change z ≫ (r • 𝟙 (K.X n)) = r • z
  rw [Linear.comp_smul, Category.comp_id]

theorem integerLinearHomologyForgetEquiv_smul (n : ℤ) (r : R)
    (a : (integerLinearHomComplex (R := R) A K).homology n) :
    integerLinearHomologyForgetEquiv (R := R) A K n (r • a) =
      HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).map (r • 𝟙 K)) n
          (integerLinearHomologyForgetEquiv (R := R) A K n a) := by
  let J := integerLinearHomComplex (R := R) A K
  let F := forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}
  let S := J.sc n
  let φ : S ⟶ S := r • 𝟙 S
  have hm : ShortComplex.homologyMap φ = r • 𝟙 S.homology := by
    rw [ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  have h := congrArg (fun g : F.obj S.homology ⟶ (S.map F).homology => g.hom a)
    (ShortComplex.mapHomologyIso_inv_naturality φ F)
  rw [integerHom_scalar_map]
  change (S.mapHomologyIso F).inv (r • a) =
    ShortComplex.homologyMap (F.mapShortComplex.map φ) ((S.mapHomologyIso F).inv a)
  rw [hm] at h
  exact h

end

end OAI.AlgebraicGeometry.Comparison.Betti.LinearHomForget.Ext
