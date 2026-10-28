import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.StratumActionAssembly
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.RelativeStratumActionAmbient

/-! # Relative Action Ambient -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.RelativeActionAmbient

noncomputable section

/-! The full corrected Presentations input gives a bounded finite-type integral
action ambient for a varying polarized family with a canonical section
embedding. The computed polynomial strata are assembled, and every
Rosati action on every reduced test is classified uniquely. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_e34_reduced_relative_action_ambient
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left) (d : ℕ)
    (hP : AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower (Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual
      A.polarization.isogeny.hom).sheaf d P.sheaf)
    {n : ℕ} (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left ⟶ P.sheaf))
    (hs : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (he : IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs).left)
    (hPresentations : Hilbert.EndomorphismEquationsInput.{0})
    (hc : ∀ x : S, IsUnit (D.conductor : S.presheaf.stalk x)) :
    ∃ Z : Over S, IsReduced Z.left ∧ LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      ∃ ρZ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback Z.hom),
        ∀ (T : Over S) [IsReduced T.left]
          (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback T.hom)),
          AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback T.hom) ρ →
            ∃! f : T ⟶ Z, Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f = ρ := by
  classical
  let BA := SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he
  let Φ := Relative.CMGraphSourcePolynomial.relativeCMGraphPolynomial D BA
  have hΦ : IsLocallyConstant Φ := Relative.CMGraphSourcePolynomial.relativeCMGraphPolynomial_isLocallyConstant D BA
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
  choose Z hr hft hqc hsep hZU ρZ hclass using
    (fun i : I => RelativeStratumActionAmbient.exists_e34_relative_stratum_action_ambient D A P d hP s hs he hPresentations hc i.val)
  let := hr
  let := hft
  let := hqc
  let := hsep
  refine IntegralModel.Finite.StratumActionAssembly.assemble_finite_stratum_action_ambient c A Z ?_ ρZ ?_
  · intro i z
    exact Subtype.ext (hZU i z)
  · intro i T hred hT ρ hρ
    apply hclass i T _ ρ hρ
    intro t
    exact congrArg Subtype.val (hT t)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.RelativeActionAmbient
