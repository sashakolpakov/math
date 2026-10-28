import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.TermModules
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ModuleHomOf
import OAI.AlgebraicGeometry.SheafCohomology.Cech.SheafDifferential

/-! # Module Differential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ModuleDifferential

noncomputable section

/-! The original sheaf-level Cech cofaces and differentials are actual
algebraic module maps, with their underlying abelian maps retained. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open _root_.TopCat.Sheaf

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens) (n : ℕ)

theorem cechCoface_smul (k : Fin (n + 2)) (V : X.Opens) (a : Γ(X, V))
    (c : (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm (TermModules.structureAbelianSheaf X) U n).obj.obj (op V)) :
    (SheafCohomology.Cech.SheafDifferential.TopCat.Sheaf.cechCoface (TermModules.structureAbelianSheaf X) U n k).hom.app (op V) (a • c) =
      a • (SheafCohomology.Cech.SheafDifferential.TopCat.Sheaf.cechCoface (TermModules.structureAbelianSheaf X) U n k).hom.app (op V) c := by
  apply (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv (TermModules.structureAbelianSheaf X) U (n + 1) V).injective
  funext i
  rw [SheafCohomology.Cech.SheafDifferential.TopCat.Sheaf.cechCoface_apply, TermModules.cechTermCoordinates_smul, TermModules.cechTermCoordinates_smul, SheafCohomology.Cech.SheafDifferential.TopCat.Sheaf.cechCoface_apply]
  let A := ∏ᶜ fun j : Fin (n + 2) => U (i j)
  let B := ∏ᶜ fun j : Fin (n + 1) => U ((i ∘ (SimplexCategory.δ k).toOrderHom.toFun) j)
  have hAB : A ≤ B := leOfHom (((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ k).toOrderHom.toFun).φ i)
  change X.presheaf.map (homOfLE (inf_le_inf_left V hAB)).op
      (X.presheaf.map (homOfLE (show V ⊓ B ≤ V from inf_le_left)).op a * _) =
    X.presheaf.map (homOfLE (show V ⊓ A ≤ V from inf_le_left)).op a * _
  rw [map_mul]
  congr 1
  exact ConcreteCategory.congr_hom ((X.presheaf.map_comp _ _).symm.trans
    (congrArg X.presheaf.map (Subsingleton.elim _ _))) a

def cechModuleCoface (k : Fin (n + 2)) : TermModules.cechTermModule X U n ⟶ TermModules.cechTermModule X U (n + 1) :=
  ModuleHomOf.moduleHomOfAbelian (SheafCohomology.Cech.SheafDifferential.TopCat.Sheaf.cechCoface (TermModules.structureAbelianSheaf X) U n k) (cechCoface_smul X U n k)

theorem cechModuleCoface_underlying (k : Fin (n + 2)) :
    (SheafOfModules.toSheaf X.ringCatSheaf).map (cechModuleCoface X U n k) =
      SheafCohomology.Cech.SheafDifferential.TopCat.Sheaf.cechCoface (TermModules.structureAbelianSheaf X) U n k :=
  ModuleHomOf.moduleHomOfAbelian_underlying _ _

def cechModuleDifferential : TermModules.cechTermModule X U n ⟶ TermModules.cechTermModule X U (n + 1) :=
  ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • cechModuleCoface X U n k

theorem cechModuleDifferential_underlying :
    (SheafOfModules.toSheaf X.ringCatSheaf).map (cechModuleDifferential X U n) =
      SheafCohomology.Cech.SheafDifferential.TopCat.Sheaf.cechDifferential (TermModules.structureAbelianSheaf X) U n := by
  unfold cechModuleDifferential SheafCohomology.Cech.SheafDifferential.TopCat.Sheaf.cechDifferential
  erw [Functor.map_sum]
  apply Finset.sum_congr rfl
  intro k _
  erw [Functor.map_zsmul, cechModuleCoface_underlying]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ModuleDifferential
