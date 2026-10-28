import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ExternalDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.GeometricRank
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.ScalarMaps
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Grading

/-! # Geometric Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.GeometricEuler

noncomputable section

/-! Serre vanishing for native stalk Tor Euler characteristics on
smooth schemes, stated using the actual geometric support dimensions.
The codimension form applies to every smooth projective presentation,
including disconnected presentations. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem euler_zero {K : Type} [Field K] {X : Scheme}
    (f : X ⟶ Spec (.of K)) (d : ℕ) [SmoothOfRelativeDimension d f]
    (x : X) (M N : ModuleCat (X.presheaf.stalk x))
    [Module.Finite (X.presheaf.stalk x) M] [Module.Finite (X.presheaf.stalk x) N]
    (A B : IrreducibleCloseds X)
    (hM : ∀ p ∈ Module.support (X.presheaf.stalk x) M, X.fromSpecStalk x p ∈ (A : Set X))
    (hN : ∀ p ∈ Module.support (X.presheaf.stalk x) N, X.fromSpecStalk x p ∈ (B : Set X))
    (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension A f + Foundations.Scheme.SupportDimension.supportTranscendenceDimension B f <
      d + Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f)
    (hi : Module.support (X.presheaf.stalk x) M ∩ Module.support (X.presheaf.stalk x) N ⊆
      {IsLocalRing.closedPoint (X.presheaf.stalk x)}) :
    Tor.Euler.euler (X.presheaf.stalk x) M N d = 0 := by
  let : Smooth f := SmoothOfRelativeDimension.smooth d f
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := d) (f := f) x
  have hu : U = ⊤ := by
    ext y
    constructor
    · intro _; trivial
    · intro _; exact (Subsingleton.elim (f x) y) ▸ e hx
  subst U
  let : Nonempty V := ⟨⟨x, hx⟩⟩
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f V
  let := Stalk.PointAlgebra.scalarAlgebra f x
  let : Algebra.IsStandardSmoothOfRelativeDimension d K Γ(X, V) :=
    Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra_standardSmooth d f V hstd
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : V)
  let : IsScalarTower K Γ(X, V) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun c => ((Stalk.ScalarMaps.germ f V x hx).commutes c).symm
  let p := hV.primeIdealOf ⟨x, hx⟩
  let : IsLocalization p.asIdeal.primeCompl (X.presheaf.stalk x) := hV.isLocalization_stalk ⟨x, hx⟩
  apply Affine.ExternalDimension.StandardSmoothEuler.euler_zero K Γ(X, V) (X.presheaf.stalk x) d p M N
    (Foundations.Scheme.SupportDimension.supportTranscendenceDimension A f) (Foundations.Scheme.SupportDimension.supportTranscendenceDimension B f)
  · intro q hq
    exact Affine.GeometricRank.bound f ⟨V, hV⟩ x hx A q (hM q hq)
  · intro q hq
    exact Affine.GeometricRank.bound f ⟨V, hV⟩ x hx B q (hN q hq)
  · rw [Affine.GeometricRank.point_dimension f ⟨V, hV⟩ x hx]
    exact hd
  · exact hi

theorem supports_at (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (d : ℕ)
    [SmoothOfRelativeDimension d X.structureMap]
    (A B C : IrreducibleCloseds X.carrier)
    (x : X.carrier) (hx : x = CycleClass.Thom.IntersectionGeometry.supportPoint C)
    (hA : x ∈ (A : Set X.carrier))
    (hB : x ∈ (B : Set X.carrier))
    (hd : X.supportCodimension C < X.supportCodimension A + X.supportCodimension B)
    (hi : Module.support (X.carrier.presheaf.stalk x)
        (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier A x hA) ∩
      Module.support (X.carrier.presheaf.stalk x)
        (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B x hB) ⊆
      {IsLocalRing.closedPoint (X.carrier.presheaf.stalk x)}) :
    Tor.Euler.euler (X.carrier.presheaf.stalk x)
      (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier A x hA)
      (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B x hB) d = 0 := by
  let := Local.TorFinite.localSupportModule_finite X.carrier A x hA
  let := Local.TorFinite.localSupportModule_finite X.carrier B x hB
  apply euler_zero X.structureMap d x _ _ A B
    (Local.SupportSpectrum.image_mem_support X.carrier A x hA)
    (Local.SupportSpectrum.image_mem_support X.carrier B x hB)
  · have hAd := Grading.supportDimension_add_codimension X d A
    have hBd := Grading.supportDimension_add_codimension X d B
    have hCd := Grading.supportDimension_add_codimension X d C
    rw [hx]
    change Foundations.Scheme.SupportDimension.supportTranscendenceDimension A X.structureMap + Foundations.Scheme.SupportDimension.supportTranscendenceDimension B X.structureMap <
      d + Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (irreducibleSetEquivPoints C)) X.structureMap
    rw [irreducibleSetEquivPoints.symm_apply_apply]
    omega
  · exact hi

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.GeometricEuler
