import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointIsogeny

/-! # Source Action -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.SourceAction.Lifts

noncomputable section

/-! The actual source-point comparison carries every coefficient action
and therefore every chosen-projector fixed section to the integral
special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets

private theorem fixed_of_iso {C : Type*} [Category C] {A B X : C}
    (e : A ≅ B) (p : A ⟶ A) (q : B ⟶ B) (h : p ≫ e.hom = e.hom ≫ q)
    (x : X ⟶ B) (hx : x ≫ q = x) : (x ≫ e.inv) ≫ p = x ≫ e.inv := by
  apply (cancel_mono e.hom).mp
  calc
    ((x ≫ e.inv) ≫ p) ≫ e.hom = (x ≫ e.inv) ≫ (p ≫ e.hom) := Category.assoc _ _ _
    _ = (x ≫ e.inv) ≫ (e.hom ≫ q) := congrArg (fun f => (x ≫ e.inv) ≫ f) h
    _ = x ≫ q := by rw [Category.assoc, e.inv_hom_id_assoc]
    _ = x := hx
    _ = (x ≫ e.inv) ≫ e.hom := by rw [Category.assoc, e.inv_hom_id, Category.comp_id]

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {b : B.R →+* R}
variable {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
variable {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x)

theorem _root_.OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifts.IntegralLift.geometricFamilyIso_action (r : NumberField.RingOfIntegers E) :
    (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map (l.action.map r) ≫
      l.geometricFamilyIso.abelian.hom =
      l.geometricFamilyIso.abelian.hom ≫ (D.pointDatum x).data.action.map r := by
  have h := l.geometricFamilyIso.equivariant r
  rw [AbelianScheme.TateComparison.PEL.PELFamilyData.pullback_action_schemeMap, Intrinsic.QuotientTargets.geometricFamily_action] at h
  change (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
      (AbelianScheme.TateComparison.End.endSchemeMap l.polarized.abelian.scheme ((AbelianScheme.TateComparison.PELAdapters.actionToEnd l.action) r)) ≫
      l.geometricFamilyIso.abelian.hom = _ at h
  rw [AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap] at h
  exact h

theorem _root_.OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifts.IntegralLift.geometricSource_action_fixed (r : NumberField.RingOfIntegers E)
    (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
    (a : T ⟶ (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x)).abelian.scheme)
    (ha : a ≫ (D.pointDatum x).data.action.map r = a) :
    (a ≫ l.geometricFamilyIso.abelian.inv) ≫
      (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map (l.action.map r) =
      a ≫ l.geometricFamilyIso.abelian.inv :=
  fixed_of_iso l.geometricFamilyIso.abelian _ _ (l.geometricFamilyIso_action r) a ha

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.SourceAction.Lifts
