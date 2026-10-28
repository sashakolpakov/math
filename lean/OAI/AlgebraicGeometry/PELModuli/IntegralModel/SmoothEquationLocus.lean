import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothEquationSupport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ClosedSubscheme
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeSmooth

/-! # Smooth Equation Locus -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothEquationLocus

noncomputable section

section

/-! Actual relative equations with a smooth source have a constructed
reduced closed classifier on every reduced test. The original parameter
is locally noetherian; the test schemes have no finiteness restriction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem exists_reduced_smooth_equation_locus
    {S : Scheme.{0}} [IsLocallyNoetherian S] {X Y : Over S}
    [Smooth X.hom] [IsSeparated Y.hom] {I : Type} (l r : I → (X ⟶ Y)) :
    ∃ Z : Over S, IsReduced Z.left ∧ IsClosedImmersion Z.hom ∧
      (∀ i, (Over.pullback Z.hom).map (l i) = (Over.pullback Z.hom).map (r i)) ∧
      ∀ (T : Over S) [IsReduced T.left],
        (∀ i, (Over.pullback T.hom).map (l i) = (Over.pullback T.hom).map (r i)) ↔
          ∃! _f : T ⟶ Z, True := by
  let W := ⋂ i, SmoothEquationSupport.smoothEquationSupport (l i) (r i)
  have hW : IsClosed W := isClosed_iInter (fun i => SmoothEquationSupport.smoothEquationSupport_closed (l i) (r i))
  obtain ⟨Z, hred, hclosed, hZ⟩ := Reduced.ClosedSubscheme.exists_reduced_closedImmersion_with_range S W hW
  let := hred
  let := hclosed
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : GeometricallyReduced X.hom :=
    Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.geometricallyReduced_of_smooth X.hom
  let : IsReduced (pullback X.hom Z.hom) := inferInstance
  have hU (i : I) : (Over.pullback Z.hom).map (l i) = (Over.pullback Z.hom).map (r i) :=
    SmoothEquationSupport.equation_of_support_range (l i) (r i) Z.hom (by
      rw [hZ]
      exact Set.iInter_subset _ i)
  refine ⟨Z, hred, hclosed, hU, ?_⟩
  intro T hT
  constructor
  · intro h
    have hr : Set.range T.hom ⊆ Set.range Z.hom := by
      rw [hZ]
      intro t ht
      exact Set.mem_iInter.mpr (fun i => SmoothEquationSupport.equation_range_subset_support (l i) (r i) T.hom (h i) ht)
    let f := Albanese.Construction.ReducedFactor.factorThroughClosed Z.hom T.hom hr
    have hf : f ≫ Z.hom = T.hom := Albanese.Construction.ReducedFactor.factorThroughClosed_comp _ _ _
    refine ⟨Over.homMk f hf, trivial, ?_⟩
    intro q _
    apply Over.OverMorphism.ext
    exact (cancel_mono Z.hom).mp (q.w.trans hf.symm)
  · rintro ⟨q, _, _⟩ i
    have h := PullbackEquationProjection.pullback_equation_precomp (l i) (r i) Z.hom q.left (hU i)
    exact (congrArg (fun t : T.left ⟶ S =>
      (Over.pullback t).map (l i) = (Over.pullback t).map (r i)) q.w).mp h

end

/-! Two actual equations with different smooth sources have a common
reduced closed locus, classified on every reduced test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem exists_reduced_two_smooth_equation_locus
    {S : Scheme.{0}} [IsLocallyNoetherian S] {X₁ Y₁ X₂ Y₂ : Over S}
    [Smooth X₁.hom] [IsSeparated Y₁.hom] [Smooth X₂.hom] [IsSeparated Y₂.hom]
    (l₁ r₁ : X₁ ⟶ Y₁) (l₂ r₂ : X₂ ⟶ Y₂) :
    ∃ Z : Over S, IsReduced Z.left ∧ IsClosedImmersion Z.hom ∧
      ((Over.pullback Z.hom).map l₁ = (Over.pullback Z.hom).map r₁ ∧
        (Over.pullback Z.hom).map l₂ = (Over.pullback Z.hom).map r₂) ∧
      ∀ (T : Over S) [IsReduced T.left],
        ((Over.pullback T.hom).map l₁ = (Over.pullback T.hom).map r₁ ∧
          (Over.pullback T.hom).map l₂ = (Over.pullback T.hom).map r₂) ↔
            ∃! _f : T ⟶ Z, True := by
  let W := SmoothEquationSupport.smoothEquationSupport l₁ r₁ ∩ SmoothEquationSupport.smoothEquationSupport l₂ r₂
  have hW : IsClosed W := (SmoothEquationSupport.smoothEquationSupport_closed l₁ r₁).inter
    (SmoothEquationSupport.smoothEquationSupport_closed l₂ r₂)
  obtain ⟨Z, hr, hc, hZ⟩ := Reduced.ClosedSubscheme.exists_reduced_closedImmersion_with_range S W hW
  let := hr
  let := hc
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : GeometricallyReduced X₁.hom :=
    Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.geometricallyReduced_of_smooth X₁.hom
  have : GeometricallyReduced X₂.hom :=
    Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.geometricallyReduced_of_smooth X₂.hom
  have : IsReduced (pullback X₁.hom Z.hom) := inferInstance
  have : IsReduced (pullback X₂.hom Z.hom) := inferInstance
  have h₁ : Set.range Z.hom ⊆ SmoothEquationSupport.smoothEquationSupport l₁ r₁ := by rw [hZ]; exact Set.inter_subset_left
  have h₂ : Set.range Z.hom ⊆ SmoothEquationSupport.smoothEquationSupport l₂ r₂ := by rw [hZ]; exact Set.inter_subset_right
  have hu₁ := SmoothEquationSupport.equation_of_support_range l₁ r₁ Z.hom h₁
  have hu₂ := SmoothEquationSupport.equation_of_support_range l₂ r₂ Z.hom h₂
  refine ⟨Z, hr, hc, ⟨hu₁, hu₂⟩, ?_⟩
  intro T _
  constructor
  · rintro ⟨ht₁, ht₂⟩
    have ht : Set.range T.hom ⊆ Set.range Z.hom := by
      rw [hZ]
      exact Set.subset_inter (SmoothEquationSupport.equation_range_subset_support l₁ r₁ T.hom ht₁)
        (SmoothEquationSupport.equation_range_subset_support l₂ r₂ T.hom ht₂)
    let f := Albanese.Construction.ReducedFactor.factorThroughClosed Z.hom T.hom ht
    have hf : f ≫ Z.hom = T.hom := Albanese.Construction.ReducedFactor.factorThroughClosed_comp _ _ _
    refine ⟨Over.homMk f hf, trivial, fun q _ => ?_⟩
    exact Over.OverMorphism.ext ((cancel_mono Z.hom).mp (q.w.trans hf.symm))
  · rintro ⟨q, _, _⟩
    have ht₁ := PullbackEquationProjection.pullback_equation_precomp l₁ r₁ Z.hom q.left hu₁
    have ht₂ := PullbackEquationProjection.pullback_equation_precomp l₂ r₂ Z.hom q.left hu₂
    exact ⟨(congrArg (fun t : T.left ⟶ S =>
      (Over.pullback t).map l₁ = (Over.pullback t).map r₁) q.w).mp ht₁,
      (congrArg (fun t : T.left ⟶ S =>
        (Over.pullback t).map l₂ = (Over.pullback t).map r₂) q.w).mp ht₂⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothEquationLocus
