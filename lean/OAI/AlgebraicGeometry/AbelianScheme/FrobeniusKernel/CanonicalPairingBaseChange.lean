import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualityIntrinsicPointValues
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizationPointBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicWeilBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalTorsionCartierIso
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePairingCharacters
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterPointBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePullbackPairingCharacters

/-! # Canonical Pairing Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalPairingBaseChange

noncomputable section

/-! Arbitrary field base change preserves the exact canonical CartierDuality
polarization pairing and the orthogonality predicate in the independent
full-kernel prescription. All multiplication covers come from the given
polarization and its actual pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom
attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

namespace Construction

attribute [local instance] DualityIntrinsicPointValues.Construction.e56PointPolarization_preserves BaseChange.Construction.pulledBackGroup

variable {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
variable {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (s : Spec (.of k') ⟶ Spec (.of k)) (n : ℕ) (hn : 0 < n)

theorem originalPolarizationPairingValue_baseChange (Q : Over (Spec (.of k')))
    (x y : ((A.pullback s).abelian.torsionFunctor n).obj (.op Q)) :
    DualityIntrinsicPointValues.Construction.originalPolarizationPairingValue (A.pullback s) n hn Q x y =
      CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s Q
        (DualityIntrinsicPointValues.Construction.originalPolarizationPairingValue A n hn ((Over.map s).obj Q)
          (A.abelian.torsionBaseChangeEquiv s Q n x) (A.abelian.torsionBaseChangeEquiv s Q n y)) := by
  let A0 := HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian
  let A1 := HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled (A.pullback s).abelian
  have h0 := CanonicalTorsionCartierIso.Construction.polarized_positiveMultiplication_cover A n hn
  have h1 := CanonicalTorsionCartierIso.Construction.polarized_positiveMultiplication_cover (A.pullback s) n hn
  have : IsFinite ((𝟙 A0.toOver) ^ n).left := h0.1
  have : Flat ((𝟙 A0.toOver) ^ n).left := h0.2.1
  have : Surjective ((𝟙 A0.toOver) ^ n).left := h0.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A0.toOver) ^ n).left := h0.2.2.2
  have : IsFinite ((𝟙 A1.toOver) ^ n).left := h1.1
  have : Flat ((𝟙 A1.toOver) ^ n).left := h1.2.1
  have : Surjective ((𝟙 A1.toOver) ^ n).left := h1.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A1.toOver) ^ n).left := h1.2.2.2
  have : IsFinite ((𝟙 A.abelian.scheme) ^ n).left := h0.1
  have : Flat ((𝟙 A.abelian.scheme) ^ n).left := h0.2.1
  have : Surjective ((𝟙 A.abelian.scheme) ^ n).left := h0.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.abelian.scheme) ^ n).left := h0.2.2.2
  have : IsFinite ((𝟙 ((Over.pullback s).obj A.abelian.scheme)) ^ n).left := h1.1
  have : Flat ((𝟙 ((Over.pullback s).obj A.abelian.scheme)) ^ n).left := h1.2.1
  have : Surjective ((𝟙 ((Over.pullback s).obj A.abelian.scheme)) ^ n).left := h1.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 ((Over.pullback s).obj A.abelian.scheme)) ^ n).left := h1.2.2.2
  let f := (𝟙 A.abelian.scheme : A.abelian.scheme ⟶ A.abelian.scheme) ^ n
  let f' := (𝟙 ((Over.pullback s).obj A.abelian.scheme) :
    (Over.pullback s).obj A.abelian.scheme ⟶ (Over.pullback s).obj A.abelian.scheme) ^ n
  have hf : f' = (Over.pullback s).map f := (CartierDuality.TorsionBaseChange.Construction.CoprimeTorsion.power_baseChange s A.abelian.scheme n).symm
  let C0 : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) :=
    DualityIntrinsicPointValues.Construction.e56NativeKernelCharacterRepresentation A0 n
  let C1 : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k'))
      (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f')) :=
    DualityIntrinsicPointValues.Construction.e56NativeKernelCharacterRepresentation A1 n
  let xp := IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint (A.pullback s).abelian n Q x
  let x0 := A.abelian.torsionBaseChangeEquiv s Q n x
  let y0 := A.abelian.torsionBaseChangeEquiv s Q n y
  obtain ⟨d, hd⟩ := ReferencePairingCharacters.Construction.originalPolarizationCharacter_exists A n hn ((Over.map s).obj Q) y0
  let dp : Q ⟶ (C0.baseChange s).dual.X := (Over.mapPullbackAdj s).homEquiv Q C0.dual.X d
  let c := CartierPicardBaseChange.Construction.nativeCartierBaseChangeAlong s f f' hf C0 C1
  have hp := CharacterPointBaseChange.Construction.originalCartierCharacterPoint_baseChange A s f f' hf C0 C1 n Q y d hd
  have hleft : DualityIntrinsicPointValues.Construction.originalPolarizationPairingValue (A.pullback s) n hn Q x y =
      C1.evaluationValue Q (dp ≫ c.hom.hom) xp := by
    apply ReferencePullbackPairingCharacters.Construction.originalPullbackPairingValue_of_character A s n hn Q x y (dp ≫ c.hom.hom)
    refine Eq.trans ?_ hp
    apply congrArg (fun z : C1.dual.X ⟶ (Over.pullback s).obj A.dual.abelian.scheme =>
      (dp ≫ c.hom.hom) ≫ z)
    rfl
  have hright := ReferencePairingCharacters.Construction.originalPolarizationPairingValue_of_character A n hn ((Over.map s).obj Q) x0 y0 d hd
  have hv := CartierPicardBaseChange.Construction.nativeCartierBaseChangeAlong_evaluation s f f' hf C0 C1 Q dp xp
  have hdp : C0.baseChangeOriginalPoint s Q dp = d :=
    ((Over.mapPullbackAdj s).homEquiv Q C0.dual.X).symm_apply_apply d
  have hx := ReferenceBaseChange.Construction.originalMultiplicationKernelPoint_baseChange A.abelian s n Q x
  have hpoint := congrArg₂ (C0.evaluationValue ((Over.map s).obj Q)) hdp hx
  exact hleft.trans (hv.trans (congrArg (CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s Q)
    (hpoint.trans hright.symm)))

theorem canonicalTorsionOrthogonal_baseChange (Q : Over (Spec (.of k')))
    (x y : ((A.pullback s).abelian.torsionFunctor n).obj (.op Q)) :
    Prescription.Construction.canonicalTorsionOrthogonal (A.pullback s) n hn Q x y ↔
      Prescription.Construction.canonicalTorsionOrthogonal A n hn ((Over.map s).obj Q)
        (A.abelian.torsionBaseChangeEquiv s Q n x) (A.abelian.torsionBaseChangeEquiv s Q n y) := by
  let e := CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s Q
  let v := DualityIntrinsicPointValues.Construction.originalPolarizationPairingValue A n hn ((Over.map s).obj Q)
    (A.abelian.torsionBaseChangeEquiv s Q n x) (A.abelian.torsionBaseChangeEquiv s Q n y)
  have he : e v = 1 ↔ v = 1 :=
    ⟨fun h => e.injective (h.trans e.map_one.symm), fun h => (congrArg e h).trans e.map_one⟩
  exact (DualityIntrinsicPointValues.Construction.canonicalTorsionOrthogonal_iff_value (A.pullback s) n hn Q x y).trans
    ((iff_of_eq (congrArg (fun z => z = 1) (originalPolarizationPairingValue_baseChange A s n hn Q x y))).trans
      (he.trans (DualityIntrinsicPointValues.Construction.canonicalTorsionOrthogonal_iff_value A n hn ((Over.map s).obj Q)
        (A.abelian.torsionBaseChangeEquiv s Q n x) (A.abelian.torsionBaseChangeEquiv s Q n y)).symm))

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalPairingBaseChange
