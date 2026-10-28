import OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.LaurentVanishing
import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectorTo

/-! # Laurent Ambient -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.LaurentAmbient.Dolbeault

noncomputable section

/-! The actual coordinate section split, expressed as ambient functions. -/

open _root_.TopologicalSpace Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_coordinateLaurent_split (U : ι → Opens ℂ) (i : ι)
    (f : (ι → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i PuncturedCauchy.Dolbeault.puncturedComplexOpen))) :
    ∃ a b : (ι → ℂ) → ℂ,
      DifferentiableOn ℂ a (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i ⊤)) ∧
      DifferentiableOn ℂ b (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i ⊤)) ∧
      (∀ x ∈ DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i ⊤), x i = 0 → b x = 0) ∧
      (∀ j, j ≠ i →
        (∀ x ∈ DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i PuncturedCauchy.Dolbeault.puncturedComplexOpen), x j = 0 → f x = 0) →
        ∀ x ∈ DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i ⊤), x j = 0 → a x = 0 ∧ b x = 0) ∧
      (∀ x ∈ DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i PuncturedCauchy.Dolbeault.puncturedComplexOpen),
        a x + b (Function.update x i (x i)⁻¹) = f x) := by
  let F := PolynomialHolomorphicSections.AnalyticLocal.functionSectionOfDifferentiable _ f hf
  let A := LaurentSections.Dolbeault.coordinatePositiveLaurentSectionMap U i F
  let B := LaurentSections.Dolbeault.coordinateNegativeLaurentSectionMap U i F
  let a := Laurent.FiberVanishing.Dolbeault.holomorphicFunctionExtension _ A
  let b := Laurent.FiberVanishing.Dolbeault.holomorphicFunctionExtension _ B
  have ha (x : DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i ⊤)) : a x.val = A.val x :=
    Holomorphic.CoefficientMem.openCoefficientExtension_apply _ A.val x
  have hb (x : DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i ⊤)) : b x.val = B.val x :=
    Holomorphic.CoefficientMem.openCoefficientExtension_apply _ B.val x
  refine ⟨a, b, Laurent.FiberVanishing.Dolbeault.holomorphicFunctionExtension_differentiable _ A,
    Laurent.FiberVanishing.Dolbeault.holomorphicFunctionExtension_differentiable _ B, ?_, ?_, ?_⟩
  · intro x hx hxi
    exact (hb ⟨x, hx⟩).trans (LaurentSections.Dolbeault.coordinateNegativeLaurentSection_zero U i F ⟨x, hx⟩ hxi)
  · intro j hji hz x hx hxj
    rw [ha ⟨x, hx⟩, hb ⟨x, hx⟩]
    exact LaurentVanishing.Dolbeault.coordinateLaurentSections_preserve_zero U i F j hji
      (fun y hy => hz y.val y.property hy) ⟨x, hx⟩ hxj
  · intro x hx
    let p : DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i PuncturedCauchy.Dolbeault.puncturedComplexOpen) := ⟨x, hx⟩
    have hfill : (LaurentSections.Dolbeault.filledCoordinatePoint U i p).val = x := LaurentSections.Dolbeault.filledCoordinatePoint_val U i p
    have hinv : (LaurentSections.Dolbeault.invertedCoordinatePoint U i p).val = Function.update x i (x i)⁻¹ := by
      funext j
      by_cases hji : j = i
      · subst j
        exact (LaurentSections.Dolbeault.invertedCoordinatePoint_same U i p).trans (Function.update_self i (x i)⁻¹ x).symm
      · exact (LaurentSections.Dolbeault.invertedCoordinatePoint_other U i p j hji).trans (Function.update_of_ne hji _ _).symm
    calc
      a x + b (Function.update x i (x i)⁻¹) =
          A.val (LaurentSections.Dolbeault.filledCoordinatePoint U i p) + B.val (LaurentSections.Dolbeault.invertedCoordinatePoint U i p) := by
        exact congrArg₂ (· + ·)
          ((congrArg a hfill.symm).trans (ha _))
          ((congrArg b hinv.symm).trans (hb _))
      _ = f x := LaurentSections.Dolbeault.coordinateLaurentSections_identity U i F p

theorem exists_laurentDomain_split (s : Finset ι) (i : ι) (hi : i ∉ s)
    (f : (ι → ℂ) → ℂ) (hf : DifferentiableOn ℂ f (Laurent.SectorTo.Dolbeault.laurentCoordinateDomain (insert i s))) :
    ∃ a b : (ι → ℂ) → ℂ,
      DifferentiableOn ℂ a (Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s) ∧
      DifferentiableOn ℂ b (Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s) ∧
      (∀ x ∈ Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s, x i = 0 → b x = 0) ∧
      (∀ j, j ≠ i →
        (∀ x ∈ Laurent.SectorTo.Dolbeault.laurentCoordinateDomain (insert i s), x j = 0 → f x = 0) →
        ∀ x ∈ Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s, x j = 0 → a x = 0 ∧ b x = 0) ∧
      (∀ x ∈ Laurent.SectorTo.Dolbeault.laurentCoordinateDomain (insert i s),
        a x + b (Function.update x i (x i)⁻¹) = f x) := by
  have hp : DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update (Laurent.SectorTo.Dolbeault.laurentCoordinateOpens s) i PuncturedCauchy.Dolbeault.puncturedComplexOpen) =
      Laurent.SectorTo.Dolbeault.laurentCoordinateDomain (insert i s) :=
    congrArg DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Laurent.SectorTo.Dolbeault.laurentCoordinateOpens_update_punctured s i)
  have he : DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update (Laurent.SectorTo.Dolbeault.laurentCoordinateOpens s) i ⊤) =
      Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s :=
    congrArg DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Laurent.SectorTo.Dolbeault.laurentCoordinateOpens_update_full s i hi)
  simpa only [hp, he] using exists_coordinateLaurent_split (Laurent.SectorTo.Dolbeault.laurentCoordinateOpens s) i f (hp ▸ hf)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.LaurentAmbient.Dolbeault
