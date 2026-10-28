import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PositiveFormula
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

/-! # Positive Formula -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.PositiveFormula

noncomputable section

/-! The original polarization supplies its normalized ample inducing line on the original field group, through the actual identity-base-change comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PositiveFormula.Construction

variable {S : Scheme.{u}} {a : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (p : A.scheme ⟶ D.abelian.scheme)

/-- The two actual maps defining the identity-fiber and original Poincare lines coincide. -/
theorem identity_family_map :
    (((Over.pullback (𝟙 S)).map p ⊗ₘ 𝟙 (A.pullback (𝟙 S)).scheme).left ≫
      AbelianModuli.HilbertConstruction.PolarizationData.poincareBaseChangeMap D (𝟙 S)) =
    (A.pullbackIdIso.hom ⊗ₘ A.pullbackIdIso.hom).left ≫ (p ⊗ₘ 𝟙 A.scheme).left := by
  rw [AbelianModuli.HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap, ← AbelianModuli.HilbertConstruction.Moduli.Coherence.poincarePullbackOverMap_id]
  have hn : (Over.pullback (𝟙 S)).map p ≫ D.abelian.pullbackIdIso.hom = A.pullbackIdIso.hom ≫ p := by
    rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackIdIso_hom, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackIdIso_hom]
    exact Over.pullbackId.hom.naturality p
  have he : ((Over.pullback (𝟙 S)).map p ⊗ₘ 𝟙 (A.pullback (𝟙 S)).scheme) ≫
      (D.abelian.pullbackIdIso.hom ⊗ₘ A.pullbackIdIso.hom) =
      (A.pullbackIdIso.hom ⊗ₘ A.pullbackIdIso.hom) ≫ (p ⊗ₘ 𝟙 A.scheme) := by
    have hl := tensorHom_comp_tensorHom ((Over.pullback (𝟙 S)).map p)
      (𝟙 (A.pullback (𝟙 S)).scheme) D.abelian.pullbackIdIso.hom A.pullbackIdIso.hom
    have hr := tensorHom_comp_tensorHom A.pullbackIdIso.hom A.pullbackIdIso.hom p (𝟙 A.scheme)
    exact hl.trans ((congrArg₂ (fun u v => u ⊗ₘ v) hn (Category.id_comp A.pullbackIdIso.hom)).trans
      ((congrArg (fun v => (A.pullbackIdIso.hom ≫ p) ⊗ₘ v)
        (Category.comp_id A.pullbackIdIso.hom)).symm.trans hr.symm))
  exact congrArg Over.Hom.left he

/-- The identity-fiber Poincare line is the actual pullback of the original line. -/
def identity_family_iso :
    (AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D p (𝟙 S)).sheaf ≅
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (A.pullbackIdIso.hom ⊗ₘ A.pullbackIdIso.hom).left
        (D.poincare.pullback (p ⊗ₘ 𝟙 A.scheme).left)).sheaf :=
  (Scheme.Modules.pullbackCongr (identity_family_map D p)).app D.poincare.sheaf ≪≫
    ((Scheme.Modules.pullbackComp (A.pullbackIdIso.hom ⊗ₘ A.pullbackIdIso.hom).left
      (p ⊗ₘ 𝟙 A.scheme).left).app D.poincare.sheaf).symm

variable {k : Type u} [Field k] [IsAlgClosed k] {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))}

/-- Geometric positivity at the identity field point gives a normalized ample inducing line on the original group. -/
theorem original_formula (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme)
    (hp : AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber D p k (𝟙 (Spec (.of k)))) :
    AbelianScheme.IsogenyQuotient.PositiveFormula.Construction.PositivePoincareFormula A.scheme (D.poincare.pullback (p ⊗ₘ 𝟙 A.scheme).left) :=
  (AbelianScheme.IsogenyQuotient.PositiveFormula.Construction.positivePoincareFormula_iff_of_iso A.pullbackIdIso
    (AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D p (𝟙 (Spec (.of k))))
    (D.poincare.pullback (p ⊗ₘ 𝟙 A.scheme).left) (identity_family_iso D p)).mp hp

/-- The original polarization itself supplies the source ample-line formula required in PoincareBundle. -/
theorem of_polarization (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin a → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) :
    AbelianScheme.IsogenyQuotient.PositiveFormula.Construction.PositivePoincareFormula A.scheme (D.poincare.pullback (pol.isogeny.hom ⊗ₘ 𝟙 A.scheme).left) :=
  original_formula D pol.isogeny.hom (pol.positive k (𝟙 (Spec (.of k))))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.PositiveFormula
