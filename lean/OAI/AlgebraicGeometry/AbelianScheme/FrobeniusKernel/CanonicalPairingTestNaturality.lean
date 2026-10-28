import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualityIntrinsicPointValues
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescription
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafEvaluation

/-! # Canonical Pairing Test Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalPairingTestNaturality.Construction

noncomputable section

/-! The exact original pairing commutes with restriction of the test
scheme, and its orthogonality predicate is invariant under test isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (n : ℕ) (hn : 0 < n)

theorem originalPolarizationPairingValue_precomp {T U : Over (Spec (.of k))} (t : U ⟶ T)
    (x y : (A.abelian.torsionFunctor n).obj (.op T)) :
    DualityIntrinsicPointValues.Construction.originalPolarizationPairingValue A n hn U
      ((A.abelian.torsionFunctor n).map t.op x) ((A.abelian.torsionFunctor n).map t.op y) =
      t ≫ DualityIntrinsicPointValues.Construction.originalPolarizationPairingValue A n hn T x y := by
  let G := CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) n
  let e := CartierDualityCanonical.Construction.e56SourceTorsionPairing A n hn
  let yp := Prescription.Construction.originalTorsionSheafPoint A.abelian n T y
  let xp := Prescription.Construction.originalTorsionSheafPoint A.abelian n T x
  have hx := Prescription.Construction.originalTorsionSheafPoint_natural A.abelian n t x
  have hy := Prescription.Construction.originalTorsionSheafPoint_natural A.abelian n t y
  have hχ := (congrArg (e.rightAdjoint.hom.app (.op U)) hy.symm).trans
    (e.rightAdjoint.hom.naturality_apply t.op yp)
  have hval := congrArg₂ (fun a b => (CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue G U a b).down) hχ hx.symm
  exact hval.trans (congrArg ULift.down
    (CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue_natural G t (e.rightAdjoint.hom.app (.op T) yp) xp))

theorem canonicalTorsionOrthogonal_testIso {T U : Over (Spec (.of k))} (e : U ≅ T)
    (x y : (A.abelian.torsionFunctor n).obj (.op T)) :
    Prescription.Construction.canonicalTorsionOrthogonal A n hn U
      ((A.abelian.torsionFunctor n).map e.hom.op x) ((A.abelian.torsionFunctor n).map e.hom.op y) ↔
      Prescription.Construction.canonicalTorsionOrthogonal A n hn T x y := by
  have hv := originalPolarizationPairingValue_precomp A n hn e.hom x y
  rw [DualityIntrinsicPointValues.Construction.canonicalTorsionOrthogonal_iff_value, DualityIntrinsicPointValues.Construction.canonicalTorsionOrthogonal_iff_value, hv]
  have ho : (1 : U ⟶ (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X) =
      e.hom ≫ (1 : T ⟶ (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X) := (MonObj.comp_one _).symm
  rw [ho]
  exact cancel_epi e.hom

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalPairingTestNaturality.Construction
