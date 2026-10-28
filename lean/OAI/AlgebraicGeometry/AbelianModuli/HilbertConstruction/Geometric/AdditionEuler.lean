import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.AdditionPowers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.NormalizedGraphPolynomial

/-! # Addition Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The positivity witness on each geometric fiber supplies the normalized
polarization formula. Thus the addition-bundle Euler polynomial is uniform
on all geometric fibers of every tame base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators
universe u
variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem Geometric.AdditionEuler.PolarizedAbelianWithLevel.geometricPullback_normalizedPolarizationFormula
    (K : Type u) [Field K] [IsAlgClosed K] (f : Spec (.of K) ⟶ S) :
    let B := A.pullback f
    ∃ L : Line.Bundles.LineBundle B.abelian.scheme.left,
      Nonempty ((((B.dual.poincareAt B.polarization.isogeny.hom).tensor
        (L.pullback (fst B.abelian.scheme B.abelian.scheme).left)).tensor
          (L.pullback (snd B.abelian.scheme B.abelian.scheme).left)).sheaf ≅
        (L.pullback μ[B.abelian.scheme].left).sheaf) := by
  let B := A.pullback f
  obtain ⟨L, _, _, ⟨e⟩⟩ := A.polarization.positive K f
  let L₁ := L.pullback (fst B.abelian.scheme B.abelian.scheme).left
  let L₂ := L.pullback (snd B.abelian.scheme B.abelian.scheme).left
  exact ⟨L, ⟨Tensor.Bifunctor.tensorModuleMapIso (Tensor.Bifunctor.tensorModuleMapIso
    (Polarization.BiextensionPoincarePoint.polarizationBiextensionAt_poincareAtIso A.dual A.polarization.isogeny.hom f)
      (Iso.refl L₁.sheaf)) (Iso.refl L₂.sheaf) ≪≫ e⟩⟩

theorem PolarizationData.PolarizedAbelianWithFullLevel.pulledBackAdditionGraphBundle_tensorPower_euler_normalized
    (hg : 0 < g) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (K : Type u) [Field K] [IsAlgClosed K] (f : Spec (.of K) ⟶ S) (m : ℕ) :
    let B := A.pullback f
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (B.abelian.scheme ⊗ B.abelian.scheme).hom
      (B.additionGraphBundle.tensorPower m).sheaf =
      (3 : ℤ) ^ g * ((2 : ℤ) ^ g * ((∏ i, δ i : ℕ) : ℤ)) ^ 2 * (m : ℤ) ^ (2 * g) := by
  obtain ⟨L, ⟨e⟩⟩ := (Geometric.AdditionEuler.PolarizedAbelianWithLevel.geometricPullback_normalizedPolarizationFormula A) K f
  exact (A.pullback f).additionGraphBundle_tensorPower_euler_normalized L e hg hN
    (Geometric.NormalizedGraphPolynomial.fieldPoint_natCast_ne_zero_of_global_unit hunit f) m

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
