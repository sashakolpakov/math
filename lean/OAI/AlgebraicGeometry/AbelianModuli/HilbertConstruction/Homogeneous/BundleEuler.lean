import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.FamilyEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdentityBaseEuler

/-! # Bundle Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! On an abelian variety over an algebraically closed field, every homogeneous line bundle preserves genuine Euler characteristic under tensor product. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u

theorem Dual.Data.DualAbelianData.homogeneousBundle_twist_euler {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
    {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))} (D : Dual.Data.DualAbelianData A)
    (L M : Line.Bundles.LineBundle A.scheme.left)
    (hM : A.IsHomogeneousPicardClass (𝟙_ (Over (Spec (.of K))))
      (Line.Bundles.LineBundle.classOf (M.pullback (pullback.snd (𝟙 (Spec (.of K))) A.scheme.hom)))) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom (L.tensor M).sheaf =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom L.sheaf := by
  have : A.scheme.left.IsSeparated := ⟨by rw [← terminal.comp_from A.scheme.hom]; infer_instance⟩
  let j := pullback.snd (𝟙 (Spec (.of K))) A.scheme.hom
  let q := pullback.fst (𝟙 (Spec (.of K))) A.scheme.hom
  calc
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom (L.tensor M).sheaf =
        CohomologyEulerCharacteristic.coefficientEulerCharacteristic q ((L.tensor M).pullback j).sheaf :=
      (IdentityBaseEuler.coefficientEulerCharacteristic_identityBase A.scheme.hom (L.tensor M)).symm
    _ = CohomologyEulerCharacteristic.coefficientEulerCharacteristic q ((L.pullback j).tensor (M.pullback j)).sheaf :=
      Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso q (Line.Bundles.LineBundle.tensorBaseChangeIso j L M)
    _ = CohomologyEulerCharacteristic.coefficientEulerCharacteristic q (L.pullback j).sheaf :=
      D.homogeneousFamily_twist_euler L (M.pullback j) hM
    _ = CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom L.sheaf :=
      IdentityBaseEuler.coefficientEulerCharacteristic_identityBase A.scheme.hom L

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
