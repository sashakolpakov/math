import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiniteResidueNondegeneracy
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELWeilResidues
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricDivision
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Etale
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Unit

/-! # Geometric Weil Nondegeneracy -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Good-prime torsion is reduced on geometric fibers, so the actual
PEL residue pairing detects the entire finite Tate evaluation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Unit.Construction

variable {k : Type} [Field k] [CharZero k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] [Smooth A.hom]

theorem GeometricWeilNondegeneracy.nativeTorsionScheme_etale_geometric (n : ℕ) (hn : 0 < n) :
    Etale (IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n).hom := by
  have : Etale (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom := TorsionQuotient.Etale.TorsionEtale.torsion_etale A n
    (IsogenyQuotient.Unit.Construction.positive_integer_unit_on_characteristic_zero_base (𝟙 (Spec (.of k))) n hn)
  let e := IsogenyQuotient.Torsion.Groups.Construction.torsionEqualizerKernelIso A n
  have : IsIso e.inv.left := (Over.forget (Spec (.of k))).map_isIso e.inv
  have he : e.inv.left ≫ (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom = (IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n).hom := e.inv.w
  rw [← he]
  infer_instance

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hgeometry : D.HasIntegralModelGeometry) [IsAlgClosed k]
  (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b) (n : ℕ)

theorem Data.SphericalPELAlbaneseData.geometricWeilResidues_detects_evaluation
    (v : Add.schemeTateModule (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q)
    (hv : ∀ w, D.geometricWeilResidues hg hgeometry b x n v w = 0) :
    Evaluation.Tate.evaluate q n v = 0 := by
  let A := (D.fiberFamily b x).abelian.scheme
  have he : Etale (IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A (q ^ n)).hom :=
    GeometricWeilNondegeneracy.nativeTorsionScheme_etale_geometric A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n)
  have hr : IsReduced (IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A (q ^ n)).left :=
    TateComparison.Etale.etale_field_source_reduced (IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A (q ^ n)).hom
  apply FiniteResidueNondegeneracy.finiteTorsionResiduePairing_nondegenerate_left A A q n
    (D.geometricTorsionPairing hg hgeometry b x n) (D.geometricTorsionPairing_isPerfect hg hgeometry b x n)
  intro y
  obtain ⟨w, rfl⟩ := GeometricDivision.geometricTate_evaluate_surjective (D.fiberFamily b x).abelian q n y
  exact hv w

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
