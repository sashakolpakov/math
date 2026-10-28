import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ModuleSupportPrimes
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiltrationAvoidance

/-! # Module Support Cover -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ModuleSupportCover

noncomputable section

/-! The full support of a finite affine module is covered by finitely
many ambient closed supports of the same lower codimension bound.
These supports can be prescribed in the geometric moving step. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiltrationAvoidance

theorem exists_data (R : Type) [CommRing R] [IsNoetherianRing R]
    (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (q : ℕ) (j : Spec (.of R) ⟶ V.carrier)
    (M : ModuleCat R) [Module.Finite R M]
    (hM : ∀ v ∈ Module.support R M, q ≤ V.supportCodimension (FiltrationAvoidance.support j v)) :
    ∃ F : Finset (IrreducibleCloseds V.carrier),
      (∀ B ∈ F, q ≤ V.supportCodimension B) ∧
      ∀ w ∈ Module.support R M, ∃ B ∈ F, j w ∈ (B : Set V.carrier) := by
  obtain ⟨T, hT, hcover⟩ := ProjectionFormula.Finite.ModuleSupportPrimes.exists_data R M
  refine ⟨T.image (FiltrationAvoidance.support j), ?_, ?_⟩
  · intro B hB
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hB
    exact hM v (hT v hv)
  · intro w hw
    obtain ⟨v, hv, hvw⟩ := hcover w hw
    exact ⟨FiltrationAvoidance.support j v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, FiltrationAvoidance.mem j w v hvw⟩

theorem avoids (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p k q : ℕ) (hkq : k < q)
    {R : Type} [CommRing R] (j : Spec (.of R) ⟶ V.carrier) (M : ModuleCat R)
    (F : Finset (IrreducibleCloseds V.carrier))
    (hF : ∀ B ∈ F, q ≤ V.supportCodimension B)
    (hcover : ∀ w ∈ Module.support R M, ∃ B ∈ F, j w ∈ (B : Set V.carrier))
    (A : V.DimensionCycleSupport p)
    (hA : ∀ B ∈ F, ∀ D : IrreducibleCloseds V.carrier,
      (D : Set V.carrier) ⊆ (A.val : Set V.carrier) ∩ (B : Set V.carrier) →
        p + V.supportCodimension B ≤ V.supportCodimension D)
    (C : V.DimensionCycleSupport (p + k)) (x : PrimeSpectrum R)
    (hx : j x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val) (hAC : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set V.carrier)) :
    x ∉ Module.support R M := by
  intro hxm
  obtain ⟨B, hB, hxB⟩ := hcover x hxm
  rw [hx] at hxB
  exact Support.HigherAvoidance.point_notMem V p k A B (hkq.trans_le (hF B hB))
    (hA B hB) C ⟨hAC, hxB⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ModuleSupportCover
