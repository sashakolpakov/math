import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Interface
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Arithmetic

/-! # Interface -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction

noncomputable section

/-!
Concrete interface for CentralAction. ActionData contains only the witnesses
in TateComparison's conclusion. Conclusion is exactly their geometric, raw-basis,
point-push, and cohomological compatibility, together with its flag clause.
It contains no finite-order condition for T3 or C0.

The active index and choice of full compact sides are explicit parameters.
Finite order is independent of the Lie ranks; the manuscript specializes
fullSide v to true exactly at its rank-three chosen compact blocks.
Geometric graphs refer to actual correspondence covers and scheme maps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]

structure ActionData (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) where
  basis : TateComparison.Local.LocalType s → TateComparison.HeckeKernel.Hecke s q
  coeff : TateComparison.Local.IntegralType s → TateComparison.Local.IntegralType s → TateComparison.Local.IntegralType s →₀ ℕ
  markingShift : D.space ≅ D.space
  TAlb : TateComparison.Local.IntegralType s → D.EndK
  rho : TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] D.EndQ
  rhoH1 : TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] Module.End ℚ D.H1

structure Conclusion (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgeometry : D.HasIntegralModelGeometry) (hgood : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : ActionData D) : Prop where
  flags : D.HasPolarizedFlagRealizations hIsogenyQuotient
  raw : ∀ t, TateComparison.HeckeKernel.IsRawDoubleCoset (TateComparison.HeckeKernel.integralLevel s q) (TateComparison.HeckeKernel.representative s q t) (A.basis t)
  coefficients : ∀ u v : TateComparison.Local.IntegralType s,
    A.basis u.val * A.basis v.val = (A.coeff u v).sum (fun w n => n • A.basis w.val)
  neighbors : ∀ (u v : TateComparison.Local.IntegralType s) (k : Type) [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b),
    (D.neighbors u b x).bind (D.neighbors v b) =
      (A.coeff u v).sum (fun w n => n • D.neighbors w b x)
  scalarIsogeny : D.CentralIsMultiplicationByQ hIsogenyQuotient hgood.2.2.1
  scalarGraph : D.IsCentralGraph A.markingShift
  scalarNeighbors : ∀ (k : Type) [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b),
    D.neighbors (TateComparison.Local.IntegralType.central s) b x = {x ≫ A.markingShift.hom}
  clears : ∀ t : TateComparison.Local.LocalType s, ∃ (n : ℕ) (u : TateComparison.Local.IntegralType s),
    A.basis (TateComparison.Local.LocalType.central s) ^ n * A.basis t = A.basis u.val
  integral : ∀ t : TateComparison.Local.IntegralType s, D.toRational (A.TAlb t) = A.rho (A.basis t.val)
  pointPush : ∀ (t : TateComparison.Local.IntegralType s) (k : Type) [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ Spec (.of K)) (j : Fin D.componentCount)
    (x y : Over.mk b ⟶ D.componentGeneric j),
    D.endPoint (A.TAlb t) (D.aPoint hgeometry j x - D.aPoint hgeometry j y) =
      ((D.neighbors t b (x ≫ D.componentInclusion j)).map (D.aTotalPoint hgeometry)).sum -
      ((D.neighbors t b (y ≫ D.componentInclusion j)).map (D.aTotalPoint hgeometry)).sum
  integralMultiplication : ∀ u v : TateComparison.Local.IntegralType s,
    A.TAlb u * A.TAlb v = (A.coeff u v).sum (fun w n => n • A.TAlb w)
  scalarUnit : IsUnit (A.rho (A.basis (TateComparison.Local.LocalType.central s)))
  cohomology : ∀ h : TateComparison.HeckeKernel.Hecke s q, D.IsRationalH1Pullback (A.rho h) (A.rhoH1 h)
  forms : ∀ (t : TateComparison.Local.IntegralType s) (ω : D.OneFormsA),
    TateComparison.Branches.IsBranchTrace (D.complexCorrespondence t) (D.albanesePullback hgeometry ω)
      (D.albanesePullback hgeometry (D.pullbackForms (A.TAlb t) ω))

/-- A graph condition on genuine algebraic correspondence morphisms. -/
def CorrespondenceIsGraph {B : Scheme} {X : Over B}
    (C : TateComparison.Correspondences.EtaleCorrespondence X) (f : X ≅ X) : Prop :=
  ∃ e : C.cover ≅ X, e.hom = C.source ∧ C.target = e.hom ≫ f.hom

/-- The actual target map, when the source of a correspondence is an iso. -/
def correspondenceMap {B : Scheme} {X : Over B}
    (C : TateComparison.Correspondences.EtaleCorrespondence X) [IsIso C.source] : X ⟶ X := inv C.source ≫ C.target

theorem correspondenceMap_source {B : Scheme} {X : Over B}
    (C : TateComparison.Correspondences.EtaleCorrespondence X) [IsIso C.source] :
    C.source ≫ correspondenceMap C = C.target := by
  simp [correspondenceMap]

theorem correspondenceMap_of_graph {B : Scheme} {X : Over B}
    (C : TateComparison.Correspondences.EtaleCorrespondence X) (f : X ≅ X) (h : CorrespondenceIsGraph C f) :
    ∃ (_ : IsIso C.source), correspondenceMap C = f.hom := by
  obtain ⟨e, he, ht⟩ := h
  have hi : IsIso C.source := he ▸ inferInstance
  refine ⟨hi, ?_⟩
  simp [correspondenceMap, ht, he]

/-- The central functions just constructed coincide with the raw basis
used by the explicitly supplied TateComparison geometric action. -/
theorem central_action_eq_raw_basis
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgeometry : D.HasIntegralModelGeometry) (hgood : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : ActionData D)
    (hTateComparison : Conclusion D hgeometry hgood hIsogenyQuotient A)
    (a : Fin s → ℤ) (h : ℤ) :
    A.rho (CentralRepresentatives.Construction.centralCoset s q a h) = A.rho (A.basis (CentralRepresentatives.Construction.centralType a h)) ∧
    A.rhoH1 (CentralRepresentatives.Construction.centralCoset s q a h) = A.rhoH1 (A.basis (CentralRepresentatives.Construction.centralType a h)) := by
  rw [CentralRepresentatives.Construction.centralCoset_eq_basis s q A.basis hTateComparison.raw]
  exact ⟨rfl, rfl⟩

/-- TateComparison's actual rational pullback relation transfers an identity power
on the Albanese to the full rational H1. No eigenline restriction occurs. -/
theorem h1_power_identity_of_albanese
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgeometry : D.HasIntegralModelGeometry) (hgood : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : ActionData D)
    (hTateComparison : Conclusion D hgeometry hgood hIsogenyQuotient A)
    (t : TateComparison.HeckeKernel.Hecke s q) (n : ℕ) (h : (A.rho t) ^ n = 1) :
    (A.rhoH1 t) ^ n = 1 := by
  have hclear : (1 : ℕ) • A.rho (t ^ n) = D.toRational (1 : D.EndK) := by
    rw [one_nsmul, map_pow, h]
    exact (map_one D.toRational).symm
  have hp := (hTateComparison.cohomology (t ^ n)).2 1 (by decide) 1 hclear
  simp only [Nat.cast_one, one_smul, map_pow, D.pullbackH1Integral_one] at hp
  exact hp

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction
