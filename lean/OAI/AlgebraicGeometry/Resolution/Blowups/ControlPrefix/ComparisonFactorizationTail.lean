import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonFactorizationTo

/-! # Comparison Factorization Tail -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Factor the already constructed tail programs using only their displayed comparison maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.comparisonFactorization_tail
    {b : ℕ} {X V S Y W T : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral V] [IsLocallyNoetherian V] [IsIntegral S] [IsLocallyNoetherian S]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {v : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {s : S ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {w : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {t : T ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {L : V.IdealSheafData} {A : S.IdealSheafData}
    {K : Y.IdealSheafData} {M : W.IdealSheafData} {B : T.IdealSheafData}
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (C : V.IdealSheafData) (hC : C ≠ ⊥)
    (E : S.IdealSheafData) (hE : E ≠ ⊥)
    (tail : Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) Y g K)
    (rest : Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup C hC) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ v)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C L hC b) W w M)
    (last : Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup E hE) (GlobalBlowup.Data.Construction.globalBlowupToBase E hE ≫ s)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal E A hE b) T t B)
    (j : V ⟶ X) (r : W ⟶ Y) (q : S ⟶ X) (u : T ⟶ Y)
    (heC : I.comap j = C) (heE : I.comap q = E)
    (hrest : tail.EtaleComparison rest (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo j I C heC hI hC) r)
    (hlast : tail.EtaleComparison last (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I E heE hI hE) u)
    (a : S ⟶ V) [Etale a] (hfactor : a ≫ j = q) (he : C.comap a = E)
    (ih : Smooth.ControlPrefix.Construction.SmoothControlPrefix.ComparisonFactorization tail) :
    ∃ z : T ⟶ W, rest.EtaleComparison last (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo a C E he hC hE) z := by
  let a' := GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo a C E he hC hE
  let : Etale a' := GlobalBlowup.EtaleMap.Construction.globalBlowupMapTo_etale a C E he hC hE
  exact ih rest last (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo j I C heC hI hC) r (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I E heE hI hE) u
    hrest hlast a' (Smooth.ControlPrefix.Construction.SmoothControlPrefix.globalBlowupMapTo_factor j a q hfactor I C E heC he heE hI hC hE)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
