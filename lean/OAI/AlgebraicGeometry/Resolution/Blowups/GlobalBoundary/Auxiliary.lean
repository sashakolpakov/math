import OAI.AlgebraicGeometry.Resolution.Blowups.Global.LogarithmicLe
import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.OldBoundaryAuxiliary
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CompanionTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.BoundaryAuxiliaryOrder

/-! # Auxiliary -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary

noncomputable section

/-! Actual global auxiliary ideals for clearing old boundary components. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Auxiliary.Construction.globalBoundaryAuxiliaryIdeal {X : Scheme} (J L : X.IdealSheafData) (m : ℕ) : X.IdealSheafData :=
  J ⊔ L ^ m

theorem Auxiliary.Construction.globalBoundaryAuxiliaryIdeal_comap {X Y : Scheme} (J L : X.IdealSheafData) (m : ℕ) (g : Y ⟶ X) :
    (Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J L m).comap g =
      Auxiliary.Construction.globalBoundaryAuxiliaryIdeal (J.comap g) (L.comap g) m := by
  rw [Auxiliary.Construction.globalBoundaryAuxiliaryIdeal, Scheme.IdealSheafData.comap_sup, IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow]
  rfl

theorem Auxiliary.Construction.globalBoundaryAuxiliaryIdeal_smooth_center_iff
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (I J L : X.IdealSheafData) [Smooth (I.subschemeι ≫ f)] (m : ℕ) (hm : 0 < m) :
    Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J L m ≤ I ^ m ↔ J ≤ I ^ m ∧ L ≤ I := by
  simpa only [Auxiliary.Construction.globalBoundaryAuxiliaryIdeal, Global.CompanionIdeal.Construction.globalMarkedIntersection, pow_one, mul_one] using
    Global.CompanionIdeal.Construction.globalMarkedIntersection_smooth_center_iff f I J L m 1 hm (by decide)

theorem Auxiliary.Construction.globalBoundaryAuxiliaryIdeal_transform
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (I J L : X.IdealSheafData) (hI : I ≠ ⊥) (m : ℕ) (hJ : J ≤ I ^ m) (hL : L ≤ I) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J L m) hI m =
      Auxiliary.Construction.globalBoundaryAuxiliaryIdeal (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I L hI 1) m := by
  simpa only [Auxiliary.Construction.globalBoundaryAuxiliaryIdeal, Global.CompanionIdeal.Construction.globalMarkedIntersection, pow_one, mul_one] using
    Global.CompanionTransform.Construction.globalBlowup_markedIntersection_transform I J L hI m 1 hJ (by simpa only [pow_one] using hL)

theorem ModelAtlas.Construction.GlobalBoundaryModelAtlas.old_boundary_auxiliary_logarithmic_bound
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β γ : Type} {D : β → X.IdealSheafData}
    (A : ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (j : β) (e : γ ↪ β) (hne : ∀ l, j ≠ e l)
    (J L : X.IdealSheafData) (hL : D j ≤ L) (m : ℕ) :
    (A.reindex e).logarithmicIdeal (Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J L m) m = ⊤ := by
  let : IsLocallyNoetherian X := A.locallyNoetherian
  apply DifferentialUnitGluing.Construction.idealSheaf_eq_top_of_openCover _ A.openCover
  intro i
  change A.indices at i
  let K := Boundary.AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal (A.affineIdeal J i) (A.affineIdeal L i) m
  have hK : (Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J L m).comap (A.map i) = Affine.QuotientKernel.Construction.affineQuotientKernel K := by
    rw [Auxiliary.Construction.globalBoundaryAuxiliaryIdeal_comap]
    change J.comap (A.map i) ⊔ (L.comap (A.map i)) ^ m = _
    rw [A.affineIdeal_eq, A.affineIdeal_eq, ← Affine.QuotientKernel.Construction.affineQuotientKernel_pow, ← Global.CompanionTransform.Construction.affineQuotientKernel_sup]
    rfl
  have hw : A.equations i j ∈ A.affineIdeal L i := by
    apply (Ideal.span_singleton_le_iff_mem _).mp
    apply (Affine.KernelOrderEquiv.Construction.affineQuotientKernel_le_iff _ _).mp
    rw [← A.component, ← A.affineIdeal_eq]
    exact Scheme.IdealSheafData.comap_mono (A.map i) hL
  have hb := (A.model i).old_boundary_auxiliary_logarithmic_bound j e hne
    (A.affineIdeal J i) (A.affineIdeal L i) hw m
  change ((A.reindex e).logarithmicIdeal (Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J L m) m).comap (A.map i) = ⊤
  rw [(A.reindex e).logarithmicIdeal_restrict_etale _ _ (A.rings i) (A.map i) (A.ground i)
    (fun l => A.equations i (e l)) (fun l => A.component i (e l)) ((A.model i).reindex e) K hK]
  change Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal ℂ
    (fun l => A.equations i (e l)) (Boundary.AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal (A.affineIdeal J i) (A.affineIdeal L i) m) m) = ⊤
  rw [hb, DifferentialUnitGluing.Construction.affineQuotientKernel_top]

theorem Auxiliary.Construction.globalBoundaryAuxiliaryIdeal_terminal_iff
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J L : X.IdealSheafData) (m : ℕ) (hm : 0 < m) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J L m) (m - 1) = ⊤ ↔
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (m - 1) ⊔ L = ⊤ := by
  have he (U : X.affineOpens) :
      (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J L m) (m - 1)).ideal U = ⊤ ↔
        (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (m - 1) ⊔ L).ideal U = ⊤ := by
    let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    let : Algebra.Smooth ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f U
    exact Blowups.Smooth.BoundaryAuxiliaryOrder.Construction.smooth_boundary_auxiliary_terminal_iff ℂ (J.ideal U) (L.ideal U) m hm
  constructor
  · intro h
    apply Scheme.IdealSheafData.ext
    funext U
    exact (he U).mp (congrArg (fun I : X.IdealSheafData => I.ideal U) h)
  · intro h
    apply Scheme.IdealSheafData.ext
    funext U
    exact (he U).mpr (congrArg (fun I : X.IdealSheafData => I.ideal U) h)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary
