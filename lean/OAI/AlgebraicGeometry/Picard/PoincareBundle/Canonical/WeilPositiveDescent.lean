import OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingPicardPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilAmpleProductLine
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilPolarizedDescent

/-! # Weil Positive Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilPositiveDescent

noncomputable section

/-! The unique type-preserving descended isogeny has an actual normalized ample Poincare formula on the quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj BigOperators

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation

attribute [local instance] Kernel.Scheme.kernelGroup
attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ}
  {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  {δ : Fin a → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DA δ) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

/-- The ample-line construction and homomorphism uniqueness prove positivity of the same isogeny whose full kernel type is preserved. -/
theorem existsUnique_positive_isogeny (n : ℕ) (hn : 0 < n) (hnd : n.Coprime ((∏ i, δ i) ^ 2))
    (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)
    (hlag : WeilData.SelfAnnihilating DA pol.isogeny n hn
      (Kernel.ContainmentMap.torsionMap f.hom n hf)) :
    ∃! m : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B DB.abelian,
      (f.hom ≫ m.hom ≫ DualMaps.representedDualMap
        (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom = pol.isogeny.hom ^ n) ∧
      m.HasPolarizationType δ ∧
      AbelianScheme.IsogenyQuotient.PositiveFormula.Construction.PositivePoincareFormula B.scheme (DB.poincare.pullback (m.hom ⊗ₘ 𝟙 B.scheme).left) := by
  obtain ⟨m, hm, hu⟩ := WeilPolarizedDescent.existsUnique_isogeny DA DB pol f n hn hnd hf hlag
  obtain ⟨N, hN, ⟨o⟩, ⟨e⟩⟩ := WeilAmpleProductLine.exists_ample_line_recovery DA pol n hn f hf hlag
  have : IsMonHom (InducingMap.hom DB N) := InducingMap.hom_isMonHom DB N
  have : IsMonHom (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA).abelian from pol.isogeny.hom) :=
    pol.isogeny.preservesGroup
  have : IsFinite (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA).abelian from pol.isogeny.hom).left :=
    pol.isogeny.finite
  have : IsMonHom (show B.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB).abelian from InducingMap.hom DB N) :=
    InducingMap.hom_isMonHom DB N
  have : IsMonHom (show B.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB).abelian from m.hom) := m.preservesGroup
  have : EffectiveEpi ((𝟙 B.scheme) ^ n) := PositiveScalar.quotient_scalar_effective
    (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA) pol.isogeny.hom f.hom n hn
  have heq := InducingPicardPullback.equation DA DB f.hom (pol.isogeny.hom ^ n) N e
  let Qh := AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication DB
  let Qv := AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication DB
  have he : InducingMap.hom DB N = m.hom :=
    @PullbackInjective.affine_pullback_injective
      (Spec (.of k)) A.scheme B.scheme DA.abelian.scheme DB.abelian.scheme
      A.group A.commutative B.group B.commutative DB.abelian.group
      (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB))
      (Line.Comparison.Bundle.fromShared DB.poincare) Qh Qv
      (SharedRepresentation.universalClass (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB) _ _) f.hom f.preservesGroup n hf
      inferInstance f.flat f.surjective inferInstance
      (InducingMap.hom DB N) m.hom (InducingMap.hom_isMonHom DB N) m.preservesGroup
      (heq.trans hm.1.symm)
  have hp := InducingMap.positive_formula DB N hN o
  rw [he] at hp
  refine ⟨m, ⟨hm.1, hm.2, hp⟩, ?_⟩
  intro r hr
  exact hu r ⟨hr.1, hr.2.1⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilPositiveDescent
