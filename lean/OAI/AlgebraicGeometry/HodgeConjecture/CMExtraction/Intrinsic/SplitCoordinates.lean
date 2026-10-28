import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SplitLabels
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitLatticeCoordinates

/-! # Split Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SplitCoordinates.ParameterChoices

noncomputable section

/-! Retained rational coordinates at all native split slots, using the
original distinguished embedding for scalar extension. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

variable (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
  {J : Type*} [Fintype J] [DecidableEq J]
  (e : (Fin 3 → E) ≃ₗ[ℚ] (J → ℚ))

def nativeSplitCoordinates : ((Fin s × Bool) → Fin 3 → Padic q) ≃ₗ[Padic q] (J → Padic q) := by
  let : Algebra E (Padic q) := (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false)).toAlgebra
  let : IsScalarTower ℚ E (Padic q) := IsScalarTower.of_algebraMap_eq
    (fun r => by change (r : Padic q) = LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false) (r : E); simp)
  exact SplitCoordinates.TestTransport.splitLabelCoordinates E (Padic q) (SplitLabels.ParameterChoices.nativeFieldAlgEmbeddingEquiv D hg hq) e

theorem nativeSplitCoordinates_rational (x : Fin 3 → E) :
    nativeSplitCoordinates E D hg hq e (fun v i => LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v (x i)) =
      fun j => algebraMap ℚ (Padic q) (e x j) := by
  let : Algebra E (Padic q) := (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false)).toAlgebra
  let : IsScalarTower ℚ E (Padic q) := IsScalarTower.of_algebraMap_eq
    (fun r => by change (r : Padic q) = LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false) (r : E); simp)
  exact SplitCoordinates.TestTransport.splitLabelCoordinates_rational E (Padic q) (SplitLabels.ParameterChoices.nativeFieldAlgEmbeddingEquiv D hg hq) e x

theorem nativeSplitCoordinates_completed (x : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :
    nativeSplitCoordinates E D hg hq e
      (fun v i => Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v) (x i)) =
      fun j => RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e x j) := by
  let : Algebra E (Padic q) := (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false)).toAlgebra
  let : IsScalarTower ℚ E (Padic q) := IsScalarTower.of_algebraMap_eq
    (fun r => by change (r : Padic q) = LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false) (r : E); simp)
  exact SplitCoordinates.TestTransport.coefficientVectorCoordinates_split E (Padic q) (SplitLabels.ParameterChoices.nativeFieldAlgEmbeddingEquiv D hg hq) e
    (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q) (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection_continuous q) x

variable (b : Module.Basis J ℤ D.reference.lattice) [Submodule.IsLattice ℚ D.reference.lattice]

theorem nativeSplitLattice_coordinates (x : (Fin s × Bool) → Fin 3 → Padic q) :
    x ∈ SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice ↔
      ∀ j, ‖nativeSplitCoordinates E D hg hq (b.extendOfIsLattice ℚ).equivFun x j‖ ≤ 1 := by
  let : Algebra E (Padic q) := (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false)).toAlgebra
  let : IsScalarTower ℚ E (Padic q) := IsScalarTower.of_algebraMap_eq
    (fun r => by change (r : Padic q) = LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false) (r : E); simp)
  exact SplitLatticeCoordinates.TestTransport.splitLatticeImage_padic_coordinates E q (SplitLabels.ParameterChoices.nativeFieldAlgEmbeddingEquiv D hg hq) D.reference.lattice b x

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SplitCoordinates.ParameterChoices
