import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ExtensionSectionDimension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.Euler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange

/-! # Section Dimension Field Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The original graph bundle's actual tensor-power section dimensions, and its positive-power Euler values, survive arbitrary field extension. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {K F : Type u} [Field K] [Field F] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
variable (φ : CommRingCat.of K ⟶ CommRingCat.of F)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_tensorPower_sections_finrank_fieldExtension (m : ℕ) :
    Module.finrank F ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (A.pullback (Spec.map φ)).abelian.scheme.hom).obj
        ((A.pullback (Spec.map φ)).graphBundle.tensorPower m).sheaf) =
      Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
        (A.graphBundle.tensorPower m).sheaf) := by
  let B := A.pullback (Spec.map φ)
  let a := pullback.fst A.abelian.scheme.hom (Spec.map φ)
  let e : ((A.graphBundle.tensorPower m).pullback a).sheaf ≅ (B.graphBundle.tensorPower m).sheaf :=
    Line.Bundles.LineBundle.powerBaseChangeIso a A.graphBundle m ≪≫
      (TensorPower.Maps.tensorPowerFunctor B.abelian.scheme.left m).mapIso (A.graphBundle_baseChangeIso (Spec.map φ)).symm
  exact (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsIso B.abelian.scheme.hom e).finrank_eq.symm.trans
    (HilbertConstruction.Field.ExtensionSectionDimension.fieldExtension_lineBundle_sections_finrank A.abelian.scheme.hom φ (A.graphBundle.tensorPower m))

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_positivePower_euler_fieldExtension
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(Spec (.of K), ⊤))) (m : ℕ) (hm : 0 < m) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (A.pullback (Spec.map φ)).abelian.scheme.hom
        ((A.pullback (Spec.map φ)).graphBundle.tensorPower m).sheaf =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom (A.graphBundle.tensorPower m).sheaf := by
  rw [(A.pullback (Spec.map φ)).graphBundle_positivePower_euler_eq_sections hN
    (Abelian.Schemes.level_unit_under_base_change (Spec.map φ) N hunit) m hm,
    A.graphBundle_positivePower_euler_eq_sections hN hunit m hm]
  exact congrArg (fun n : ℕ => (n : ℤ))
    (A.graphBundle_tensorPower_sections_finrank_fieldExtension φ m)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
