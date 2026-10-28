import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.GeometricEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.Prime

/-! # Higher Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.HigherEuler

noncomputable section

/-! Higher-codimension affine prime factors have zero native Euler
contribution whenever their localized pairing is isolated. This uses
Serre vanishing and requires no additional positioning of that factor. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiltrationAvoidance

theorem zero (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m V.structureMap]
    (R : Type) [CommRing R] (j : Spec (.of R) ⟶ V.carrier) [IsOpenImmersion j]
    (w : PrimeSpectrum R) (hw : q < V.supportCodimension (FiltrationAvoidance.support j w))
    (A : V.DimensionCycleSupport p) (A₀ : IrreducibleCloseds (Spec (.of R)))
    (hA : j (CycleClass.Thom.IntersectionGeometry.supportPoint A₀) = CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
    (C : V.DimensionCycleSupport (p + q)) (x : PrimeSpectrum R)
    (hx : j x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val) (hxA : x ∈ (A₀ : Set (Spec (.of R))))
    (hi : letI : Algebra R ((Spec (.of R)).presheaf.stalk x) := (StructureSheaf.toStalk R x).hom.toAlgebra
      Module.support ((Spec (.of R)).presheaf.stalk x)
        ((Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj (.of R (R ⧸ w.asIdeal))) ∩
      Module.support ((Spec (.of R)).presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) A₀ x hxA) ⊆
        {IsLocalRing.closedPoint ((Spec (.of R)).presheaf.stalk x)}) :
    letI : Algebra R ((Spec (.of R)).presheaf.stalk x) := (StructureSheaf.toStalk R x).hom.toAlgebra
    Tor.Euler.euler ((Spec (.of R)).presheaf.stalk x)
      ((Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj (.of R (R ⧸ w.asIdeal)))
      (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) A₀ x hxA) m = 0 := by
  let S := (Spec (.of R)).presheaf.stalk x
  let : Algebra R S := (StructureSheaf.toStalk R x).hom.toAlgebra
  let : IsLocalization x.asIdeal.primeCompl S := by
    change IsLocalization x.asIdeal.primeCompl ((structurePresheafInCommRingCat R).stalk x)
    infer_instance
  by_cases hwx : w.asIdeal ≤ x.asIdeal
  · let B := FiltrationAvoidance.support j w
    let B₀ := SupportStalk.support R w
    have hxB₀ := SupportStalk.mem R w x hwx
    have hB : j (CycleClass.Thom.IntersectionGeometry.supportPoint B₀) = CycleClass.Thom.IntersectionGeometry.supportPoint B := by
      rw [SupportStalk.point]
      exact (irreducibleSetEquivPoints.apply_symm_apply (j w)).symm
    have hxB : j x ∈ (B : Set V.carrier) := (Prime.mem_iff j w x).mpr hwx
    have hxAj : j x ∈ (A.val : Set V.carrier) :=
      CoverIsolation.image_subset j A₀ A.val hA ⟨x, hxA, rfl⟩
    have he := PrincipalBaseChange.SupportOrder.baseEquiv R w x hwx
    rw [he.support_eq] at hi
    rw [PrimeFiltrationEuler.euler_iso_left S he.toModuleIso (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) A₀ x hxA) m,
      Open.SupportEuler.euler j B₀ A₀ B A.val hB hA x hxB₀ hxA hxB hxAj m]
    apply Smooth.GeometricEuler.supports_at V m B A.val C.val (j x) hx hxB hxAj
    · have hAd := A.property
      have hCd := C.property
      change q < V.supportCodimension B at hw
      omega
    · exact Open.SupportEuler.isolated j B₀ A₀ B A.val hB hA x hxB₀ hxA hxB hxAj hi
  · exact LocalizedFixedFiltration.prime_euler_zero R S x w hwx _ m

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.HigherEuler
