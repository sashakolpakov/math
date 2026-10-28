import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BaseChangeSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedSupportCover
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricSupportLocalization

/-! # Cover Isolation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.CoverIsolation

noncomputable section

/-! Properness against the full affine support cover gives isolated
native stalk intersections for every module in the chart expansion. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem image_subset {Y X : Scheme} (j : Y ⟶ X)
    (A : IrreducibleCloseds Y) (B : IrreducibleCloseds X)
    (h : j (CycleClass.Thom.IntersectionGeometry.supportPoint A) = CycleClass.Thom.IntersectionGeometry.supportPoint B) : j '' (A : Set Y) ⊆ (B : Set X) := by
  rintro _ ⟨y, hy, rfl⟩
  have hs := ((A.isIrreducible.isGenericPoint_genericPoint A.isClosed).specializes hy).map j.continuous
  change j (CycleClass.Thom.IntersectionGeometry.supportPoint A) ⤳ j y at hs
  rw [h] at hs
  exact hs.mem_closed B.isClosed (B.isIrreducible.isGenericPoint_genericPoint B.isClosed).mem

theorem isolated (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m V.structureMap]
    (R : Type) [CommRing R] (j : Spec (.of R) ⟶ V.carrier) [IsOpenImmersion j]
    (M : ModuleCat R) [Module.Finite R M]
    (F : Finset (IrreducibleCloseds V.carrier))
    (hF : ∀ B ∈ F, q ≤ V.supportCodimension B)
    (hcover : ∀ w ∈ Module.support R M, ∃ B ∈ F, j w ∈ (B : Set V.carrier))
    (A : V.DimensionCycleSupport p) (A₀ : IrreducibleCloseds (Spec (.of R)))
    (hA : j (CycleClass.Thom.IntersectionGeometry.supportPoint A₀) = CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
    (hproper : ∀ B ∈ F, ∀ D : IrreducibleCloseds V.carrier,
      (D : Set V.carrier) ⊆ (A.val : Set V.carrier) ∩ (B : Set V.carrier) →
        p + V.supportCodimension B ≤ V.supportCodimension D)
    (C : V.DimensionCycleSupport (p + q)) (x : PrimeSpectrum R)
    (hx : j x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val) (hxA : x ∈ (A₀ : Set (Spec (.of R)))) :
    letI : Algebra R ((Spec (.of R)).presheaf.stalk x) := (StructureSheaf.toStalk R x).hom.toAlgebra
    Module.support ((Spec (.of R)).presheaf.stalk x)
        ((Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj M) ∩
      Module.support ((Spec (.of R)).presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) A₀ x hxA) ⊆
        {IsLocalRing.closedPoint ((Spec (.of R)).presheaf.stalk x)} := by
  let S := (Spec (.of R)).presheaf.stalk x
  let : Algebra R S := (StructureSheaf.toStalk R x).hom.toAlgebra
  let u : Spec (.of S) ⟶ V.carrier := (Spec (.of R)).fromSpecStalk x ≫ j
  have hu : Function.Injective u :=
    j.isOpenEmbedding.injective.comp ((Spec (.of R)).fromSpecStalk x).isEmbedding.injective
  have hc : u (IsLocalRing.closedPoint S) = CycleClass.Thom.IntersectionGeometry.supportPoint C.val := by
    change j ((Spec (.of R)).fromSpecStalk x (IsLocalRing.closedPoint S)) = _
    rw [Scheme.fromSpecStalk_closedPoint, hx]
  apply IsolatedSupportCover.isolated V m p q A C S u hu hc
    ((Flat.Extension.baseChange R S).obj M) (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) A₀ x hxA) F hF hproper
  · intro z hz
    obtain ⟨B, hB, hm⟩ := hcover _ (BaseChangeSupport.mem_image R S M z hz)
    refine ⟨B, hB, ?_⟩
    change j ((Spec (.of R)).fromSpecStalk x z) ∈ (B : Set V.carrier)
    rw [Spec.fromSpecStalk_eq']
    exact hm
  · intro z hz
    apply image_subset j A₀ A.val hA
    exact ⟨(Spec (.of R)).fromSpecStalk x z,
      Local.SupportSpectrum.image_mem_support (Spec (.of R)) A₀ x hxA z hz, rfl⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.CoverIsolation
