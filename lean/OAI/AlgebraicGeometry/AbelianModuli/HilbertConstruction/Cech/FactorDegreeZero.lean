import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafTermCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafFactorRestriction

/-! # Factor Degree Zero -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.FactorDegreeZero.IntrinsicCech

noncomputable section

/-! Degree-zero cohomology of the restriction-pushforward open factors is
the original sheaf of sections, naturally in the open set. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}} (F : X.Sheaf AddCommGrpCat.{u})

def cechFactorTopOpenIso (A : Opens X) :
    ((IntrinsicCech.SheafComplex.cechFactorPresheaf F).obj (op A)).obj.obj (op ⊤) ≅ F.obj.obj (op A) :=
  SheafFactorRestriction.IntrinsicCech.cechOpenFactorSectionsIso F A ⊤ ≪≫ F.obj.mapIso (eqToIso (congrArg op (top_inf_eq A)))

theorem cechFactorTopOpenIso_naturality {A B : Opens X} (h : A ≤ B) :
    (SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction F h).hom.app (op ⊤) ≫ (cechFactorTopOpenIso F A).hom =
      (cechFactorTopOpenIso F B).hom ≫ F.obj.map (homOfLE h).op := by
  have he : (SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction F h).hom.app (op ⊤) ≫
      (SheafFactorRestriction.IntrinsicCech.cechOpenFactorSectionsIso F A ⊤).hom =
    (SheafFactorRestriction.IntrinsicCech.cechOpenFactorSectionsIso F B ⊤).hom ≫
      F.obj.map (homOfLE (inf_le_inf_left ⊤ h)).op := by
    apply ConcreteCategory.hom_ext
    intro x
    exact SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction_sections_mapIso F h ⊤ x
  change (SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction F h).hom.app (op ⊤) ≫
      ((SheafFactorRestriction.IntrinsicCech.cechOpenFactorSectionsIso F A ⊤).hom ≫ F.obj.map _) =
    ((SheafFactorRestriction.IntrinsicCech.cechOpenFactorSectionsIso F B ⊤).hom ≫ F.obj.map _) ≫ F.obj.map _
  rw [← Category.assoc, he, Category.assoc, Category.assoc]
  congr 1
  rw [← F.obj.map_comp, ← F.obj.map_comp]
  exact F.obj.congr_map (Subsingleton.elim _ _)

private def zeroCohomologySectionsIso (G : X.Sheaf AddCommGrpCat.{u}) :
    (SheafTermCohomology.IntrinsicCech.nativeSheafCohomologyFunctor X 0).obj G ≅ G.obj.obj (op ⊤) :=
  (CategoryTheory.Sheaf.H.equiv₀ G
    (isTerminalTop : IsTerminal (⊤ : Opens X))).toAddCommGrpIso

private theorem zeroCohomologySectionsIso_naturality
    {G H : X.Sheaf AddCommGrpCat.{u}} (r : G ⟶ H) :
    (SheafTermCohomology.IntrinsicCech.nativeSheafCohomologyFunctor X 0).map r ≫ (zeroCohomologySectionsIso H).hom =
      (zeroCohomologySectionsIso G).hom ≫ r.hom.app (op ⊤) := by
  apply ConcreteCategory.hom_ext
  intro x
  exact (CategoryTheory.Sheaf.H.equiv₀_naturality isTerminalTop r x).symm

def cechFactorZeroCohomologyIso (A : Opens X) :
    (SheafTermCohomology.IntrinsicCech.cechFactorCohomologyPresheaf F 0).obj (op A) ≅ F.obj.obj (op A) :=
  zeroCohomologySectionsIso ((IntrinsicCech.SheafComplex.cechFactorPresheaf F).obj (op A)) ≪≫ cechFactorTopOpenIso F A

theorem cechFactorZeroCohomologyIso_naturality {A B : Opens X} (h : A ≤ B) :
    (SheafTermCohomology.IntrinsicCech.cechFactorCohomologyPresheaf F 0).map (homOfLE h).op ≫
      (cechFactorZeroCohomologyIso F A).hom =
    (cechFactorZeroCohomologyIso F B).hom ≫ F.obj.map (homOfLE h).op := by
  let r := SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction F h
  let zA := zeroCohomologySectionsIso ((IntrinsicCech.SheafComplex.cechFactorPresheaf F).obj (op A))
  let zB := zeroCohomologySectionsIso ((IntrinsicCech.SheafComplex.cechFactorPresheaf F).obj (op B))
  have hz : (SheafTermCohomology.IntrinsicCech.nativeSheafCohomologyFunctor X 0).map r ≫ zA.hom =
      zB.hom ≫ r.hom.app (op ⊤) := zeroCohomologySectionsIso_naturality r
  change (SheafTermCohomology.IntrinsicCech.nativeSheafCohomologyFunctor X 0).map r ≫
      (zA.hom ≫ (cechFactorTopOpenIso F A).hom) =
    (zB.hom ≫ (cechFactorTopOpenIso F B).hom) ≫ F.obj.map (homOfLE h).op
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (cechFactorTopOpenIso F A).hom) hz).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => zB.hom ≫ k) (cechFactorTopOpenIso_naturality F h)).trans
          (Category.assoc _ _ _).symm)))

def cechFactorZeroCohomologyPresheafIso : SheafTermCohomology.IntrinsicCech.cechFactorCohomologyPresheaf F 0 ≅ F.obj :=
  NatIso.ofComponents (fun A => cechFactorZeroCohomologyIso F A.unop)
    (fun {A B} i => cechFactorZeroCohomologyIso_naturality F
      (A := B.unop) (B := A.unop) (leOfHom i.unop))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.FactorDegreeZero.IntrinsicCech
