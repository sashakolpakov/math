import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointBundleFaithfulness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointSectionTriviality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsFunctor

/-! # Nontrivial Poincare Point Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A nonidentity dual point has no nonzero global section in its actual Poincare point bundle. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
variable {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))} (D : Dual.Data.DualAbelianData A)
variable (f : 𝟙_ (Over (Spec (.of K))) ⟶ D.abelian.scheme) (hf : f ≠ 1)

include hf

theorem Dual.Data.DualAbelianData.poincarePointBundle_section_eq_zero
    (s : Line.Bundles.structureModule A.scheme.left ⟶ (D.poincarePointBundle f).sheaf) : s = 0 := by
  classical
  by_contra hs
  obtain ⟨e⟩ := D.poincarePointBundle_trivial_of_nonzero_section f s hs
  apply hf
  apply D.poincarePointBundle_class_injective
  exact Quotient.sound ⟨e ≪≫ D.poincarePointBundle_oneIso.symm⟩

theorem Dual.Data.DualAbelianData.poincarePointBundle_sections_isZero :
    IsZero ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.scheme.hom).obj (D.poincarePointBundle f).sheaf) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  constructor
  intro z w
  apply (Global.Sections.moduleSectionHomEquiv (D.poincarePointBundle f).sheaf).symm.injective
  exact (D.poincarePointBundle_section_eq_zero f hf
    ((Global.Sections.moduleSectionHomEquiv (D.poincarePointBundle f).sheaf).symm z)).trans
      (D.poincarePointBundle_section_eq_zero f hf
        ((Global.Sections.moduleSectionHomEquiv (D.poincarePointBundle f).sheaf).symm w)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
