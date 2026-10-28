import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.FactorDegreeZero

/-! # Factor Sheaf Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.FactorSheafNaturality

noncomputable section

/-! Restriction-pushforward open factors and their section comparisons are
natural in the underlying sheaf, as well as in the open parameter. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
set_option backward.isDefEq.respectTransparency false

namespace IntrinsicCech
variable {X : TopCat.{u}} {F G : X.Sheaf AddCommGrpCat.{u}}

def cechOpenFactorMap (e : F ⟶ G) (A : Opens X) :
    (IntrinsicCech.SheafComplex.cechFactorPresheaf F).obj (op A) ⟶ (IntrinsicCech.SheafComplex.cechFactorPresheaf G).obj (op A) :=
  (TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat A.isOpenEmbedding ⋙
    TopCat.Sheaf.pushforward AddCommGrpCat A.inclusion').map e

theorem cechOpenFactorSectionsIso_sheaf_naturality
    (e : F ⟶ G) (A V : Opens X) :
    (cechOpenFactorMap e A).hom.app (op V) ≫ (Cech.SheafFactorRestriction.IntrinsicCech.cechOpenFactorSectionsIso G A V).hom =
      (Cech.SheafFactorRestriction.IntrinsicCech.cechOpenFactorSectionsIso F A V).hom ≫ e.hom.app (op (V ⊓ A)) := by
  change e.hom.app _ ≫ G.obj.map _ = F.obj.map _ ≫ e.hom.app _
  exact (e.hom.naturality _).symm

theorem cechOpenFactorMap_restrict (e : F ⟶ G) {A B : Opens X} (h : A ≤ B) :
    Cech.SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction F h ≫ cechOpenFactorMap e A =
      cechOpenFactorMap e B ≫ Cech.SheafFactorRestriction.IntrinsicCech.cechTermFactorRestriction G h := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext V
  change F.obj.map _ ≫ e.hom.app _ = e.hom.app _ ≫ G.obj.map _
  exact e.hom.naturality _

def cechFactorPresheafMap (e : F ⟶ G) : IntrinsicCech.SheafComplex.cechFactorPresheaf F ⟶ IntrinsicCech.SheafComplex.cechFactorPresheaf G where
  app A := cechOpenFactorMap e A.unop
  naturality _A _B i := cechOpenFactorMap_restrict e (leOfHom i.unop)

theorem cechFactorTopOpenIso_sheaf_naturality (e : F ⟶ G) (A : Opens X) :
    (cechOpenFactorMap e A).hom.app (op ⊤) ≫ (Cech.FactorDegreeZero.IntrinsicCech.cechFactorTopOpenIso G A).hom =
      (Cech.FactorDegreeZero.IntrinsicCech.cechFactorTopOpenIso F A).hom ≫ e.hom.app (op A) := by
  change (cechOpenFactorMap e A).hom.app (op ⊤) ≫
      ((Cech.SheafFactorRestriction.IntrinsicCech.cechOpenFactorSectionsIso G A ⊤).hom ≫ G.obj.map _) =
    ((Cech.SheafFactorRestriction.IntrinsicCech.cechOpenFactorSectionsIso F A ⊤).hom ≫ F.obj.map _) ≫ e.hom.app (op A)
  rw [← Category.assoc, cechOpenFactorSectionsIso_sheaf_naturality, Category.assoc,
    ← e.hom.naturality]
  exact (Category.assoc _ _ _).symm

private def zeroCohomologySectionsIso (F : X.Sheaf AddCommGrpCat.{u}) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 0).obj F ≅
      F.obj.obj (op ⊤) :=
  (CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop).toAddCommGrpIso

private theorem zeroCohomology_sections_naturality (e : F ⟶ G) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 0).map e ≫
        (zeroCohomologySectionsIso G).hom =
      (zeroCohomologySectionsIso F).hom ≫
        e.hom.app (op ⊤) := by
  apply ConcreteCategory.hom_ext
  intro x
  exact (CategoryTheory.Sheaf.H.equiv₀_naturality isTerminalTop e x).symm

private theorem compose_naturality {C : Type*} [Category C]
    {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C}
    (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂) (c : Z₁ ⟶ Z₂)
    (u₁ : X₁ ⟶ Y₁) (u₂ : X₂ ⟶ Y₂) (v₁ : Y₁ ⟶ Z₁) (v₂ : Y₂ ⟶ Z₂)
    (hu : a ≫ u₂ = u₁ ≫ b) (hv : b ≫ v₂ = v₁ ≫ c) :
    a ≫ (u₂ ≫ v₂) = (u₁ ≫ v₁) ≫ c := by
  rw [← Category.assoc, hu, Category.assoc, hv, ← Category.assoc]

private theorem zeroSections_comp_naturality
    {A B : AddCommGrpCat.{u}} (r : F ⟶ G) (f : A ⟶ B)
    (eF : F.obj.obj (op ⊤) ≅ A) (eG : G.obj.obj (op ⊤) ≅ B)
    (h : r.hom.app (op ⊤) ≫ eG.hom = eF.hom ≫ f) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 0).map r ≫
        ((zeroCohomologySectionsIso G) ≪≫ eG).hom =
      ((zeroCohomologySectionsIso F) ≪≫ eF).hom ≫ f :=
  compose_naturality _ _ _ _ _ _ _ (zeroCohomology_sections_naturality r) h

theorem cechFactorZeroCohomologyIso_sheaf_naturality (e : F ⟶ G) (A : Opens X) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 0).map (cechOpenFactorMap e A) ≫
      (Cech.FactorDegreeZero.IntrinsicCech.cechFactorZeroCohomologyIso G A).hom =
    (Cech.FactorDegreeZero.IntrinsicCech.cechFactorZeroCohomologyIso F A).hom ≫ e.hom.app (op A) := by
  have result := zeroSections_comp_naturality
    (cechOpenFactorMap e A) (e.hom.app (op A))
    (Cech.FactorDegreeZero.IntrinsicCech.cechFactorTopOpenIso F A) (Cech.FactorDegreeZero.IntrinsicCech.cechFactorTopOpenIso G A)
    (cechFactorTopOpenIso_sheaf_naturality e A)
  exact result

end IntrinsicCech

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.FactorSheafNaturality
