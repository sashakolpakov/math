import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StratumIntegralActionAmbient
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.StratumActionAssembly

/-! # Integral Action Ambient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.IntegralActionAmbient

noncomputable section

/-! Construct a finite-type integral-action ambient for a polarized
family with a canonical section embedding. The finitely many computed
graph-polynomial strata cover every Rosati action on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_relative_integral_action_ambient
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    (D : PELModuli.IntegralModel.CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    {g N : ℕ} {δ : Fin g → ℕ} (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (P : HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left) (d : ℕ)
    (hP : HilbertConstruction.Tensor.Powers.IsTensorPower (PELModuli.IntegralModel.Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual
      A.polarization.isogeny.hom).sheaf d P.sheaf)
    {n : ℕ} (s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left ⟶ P.sheaf))
    (hs : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (he : IsClosedImmersion (HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs).left)
    (hc : ∀ x : S, IsUnit (D.conductor : S.presheaf.stalk x)) :
    ∃ Z : Over S, LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      ∃ ρZ : ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback Z.hom),
        ∀ (T : Over S)
          (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback T.hom)),
          ActionData.RosatiConjugation (A.pullback T.hom) ρ →
            ∃! f : T ⟶ Z, PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f = ρ := by
  classical
  let BA := PELModuli.IntegralModel.SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he
  let Φ := PELModuli.IntegralModel.Relative.CMGraphSourcePolynomial.relativeCMGraphPolynomial D BA
  have hΦ : IsLocallyConstant Φ := PELModuli.IntegralModel.Relative.CMGraphSourcePolynomial.relativeCMGraphPolynomial_isLocallyConstant D BA
  let I := Set.range Φ
  let : Finite I := hΦ.range_finite.to_subtype
  let c : LocallyConstant S I :=
    { toFun := fun x => ⟨Φ x, x, rfl⟩
      isLocallyConstant := by
        apply IsLocallyConstant.iff_isOpen_fiber.mpr
        intro i
        have heq : (fun x => (⟨Φ x, x, rfl⟩ : I)) ⁻¹' {i} = {x | Φ x = i.val} := by
          ext x
          exact Subtype.ext_iff
        rw [heq]
        exact hΦ.isOpen_fiber i.val }
  choose Z hft hqc hsep hZU ρZ hclass using
    (fun i : I => StratumIntegralActionAmbient.exists_stratum_integral_action_ambient D A P d hP s hs he hc i.val)
  let := hft
  let := hqc
  let := hsep
  refine ReferenceFamily.Finite.StratumActionAssembly.assemble_all_test_stratum_action_ambient c A Z ?_ ρZ ?_
  · intro i z
    exact Subtype.ext (hZU i z)
  · intro i T hT ρ hρ
    apply hclass i T _ ρ hρ
    intro t
    exact congrArg Subtype.val (hT t)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.IntegralActionAmbient
