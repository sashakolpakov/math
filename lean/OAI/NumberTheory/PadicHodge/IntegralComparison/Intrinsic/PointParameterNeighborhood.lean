import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.PrincipalSectionAlgebra
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CenteredParameterRegularity
import OAI.NumberTheory.PadicHodge.IntegralComparison.CompositeSectionKernel
import OAI.NumberTheory.PadicHodge.IntegralComparison.IdealSheafPrincipalEquations

/-! # Point Parameter Neighborhood -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.PointParameterNeighborhood

noncomputable section

/-! A genuine ambient principal neighborhood of a section has regular
normal equations followed by lifts of its centered étale parameters.
Their concatenation generates the literal section kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y) [IsClosedImmersion f.left]
  (s : Spec (CommRingCat.of R) ⟶ X.left) (hs : s ≫ X.hom = 𝟙 _)
  (U : Y.left.Opens) (hU : IsAffineOpen U) (hsU : ⊤ ≤ s ⁻¹ᵁ (f.left ⁻¹ᵁ U))
  (σ : Type u) [Fintype σ] [Algebra (MvPolynomial σ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial σ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial σ R) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  {c m : ℕ} (a : Fin c → Γ(Y.left, U)) (e : Fin m ≃ σ)

def preimageRestriction (r : Γ(Y.left, U)) :
    (f.left ⁻¹ᵁ Y.left.basicOpen r) ⟶ (f.left ⁻¹ᵁ U) :=
  homOfLE (f.left.preimage_mono (Y.left.basicOpen_le r))

def quotientParameter (r : Γ(Y.left, U)) (j : Fin m) :
    SmoothClosedSections.ring R X (f.left ⁻¹ᵁ Y.left.basicOpen r) :=
  ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map (preimageRestriction R X Y f U r).op).hom
    (IntegralComparison.Etale.CoordinateSectionKernel.parameter
      (SectionEvaluation.evaluation R X s hs (f.left ⁻¹ᵁ U) hsU) (e j))

structure Data (r : Γ(Y.left, U)) where
  contains : ⊤ ≤ s ⁻¹ᵁ (f.left ⁻¹ᵁ Y.left.basicOpen r)
  parameter : Fin m → Γ(Y.left, Y.left.basicOpen r)
  lift : ∀ j, f.left.app (Y.left.basicOpen r) (parameter j) =
    quotientParameter R X Y f s hs U hsU σ e r j
  kernel : Ideal.span (Set.range
      (Fin.append (IdealSheafPrincipalEquations.sequence U r a) parameter)) =
    RingHom.ker ((SectionEvaluation.evaluation R X s hs
      (f.left ⁻¹ᵁ Y.left.basicOpen r) contains).toRingHom.comp
        (f.left.app (Y.left.basicOpen r)).hom)
  regular : RingTheory.Sequence.IsWeaklyRegular Γ(Y.left, Y.left.basicOpen r)
    (List.ofFn (Fin.append (IdealSheafPrincipalEquations.sequence U r a) parameter))

include hU in
theorem exists_principal
    (ha : Ideal.span (Set.range a) = f.left.ker.ideal ⟨U, hU⟩)
    (hareg : RingTheory.Sequence.IsWeaklyRegular Γ(Y.left, U) (List.ofFn a)) :
    ∃ r : Γ(Y.left, U), Nonempty (Data R X Y f s hs U hsU σ a e r) := by
  let ε := SectionEvaluation.evaluation R X s hs (f.left ⁻¹ᵁ U) hsU
  let t : Fin m → SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U) :=
    fun j => IntegralComparison.Etale.CoordinateSectionKernel.parameter ε (e j)
  have hrange : Set.range t = Set.range (IntegralComparison.Etale.CoordinateSectionKernel.parameter (σ := σ) ε) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e j, rfl⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨i, rfl⟩ := e.surjective j
      exact ⟨i, rfl⟩
  obtain ⟨u, hu, hann⟩ := IntegralComparison.Etale.CoordinateSectionKernel.exists_principal (σ := σ) ε
  obtain ⟨r, hr⟩ := f.left.app_surjective U hU u
  have hpre : f.left ⁻¹ᵁ Y.left.basicOpen r = X.left.basicOpen u := by
    rw [Scheme.preimage_basicOpen, hr]
  have hcontains : ⊤ ≤ s ⁻¹ᵁ (f.left ⁻¹ᵁ Y.left.basicOpen r) := by
    rw [hpre]
    exact SectionEvaluation.principal_contains R X s hs (f.left ⁻¹ᵁ U) hsU u hu
  let i := preimageRestriction R X Y f U r
  let := IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionAlgebra R X i
  let := PrincipalSectionAlgebra.localization R X i (hU.preimage f.left) u hpre
  let : Module.Flat (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U)) (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ Y.left.basicOpen r)) :=
    IsLocalization.flat (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ Y.left.basicOpen r)) (Submonoid.powers u)
  have hI : Ideal.span (Set.range t) ≤ RingHom.ker ε.toRingHom := by
    rw [hrange, ← IntegralComparison.Etale.CoordinateSectionKernel.ideal_eq_span]
    exact IntegralComparison.Etale.CoordinateSectionKernel.ideal_le_kernel (σ := σ) ε
  have hann' : ∀ x, ε x = 0 → u * x ∈ Ideal.span (Set.range t) := by
    simpa only [hrange] using hann
  have hk := PrincipalSectionAlgebra.kernel R X i (hU.preimage f.left) u hpre
    s hs hsU hcontains (Ideal.span (Set.range t)) hI hann'
  have ht : Ideal.span (Set.range (quotientParameter R X Y f s hs U hsU σ e r)) =
      RingHom.ker (SectionEvaluation.evaluation R X s hs
        (f.left ⁻¹ᵁ Y.left.basicOpen r) hcontains).toRingHom := by
    rw [hk, Ideal.map_span, ← Set.range_comp]
    rfl
  have htreg : RingTheory.Sequence.IsWeaklyRegular (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ Y.left.basicOpen r))
      (List.ofFn (quotientParameter R X Y f s hs U hsU σ e r)) := by
    change RingTheory.Sequence.IsWeaklyRegular (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ Y.left.basicOpen r))
      (List.ofFn (fun j => algebraMap (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))
        (SmoothClosedSections.ring R X (f.left ⁻¹ᵁ Y.left.basicOpen r)) (t j)))
    have h := (IntegralComparison.Etale.CenteredParameterRegularity.regular ε e).of_flat
      (S := SmoothClosedSections.ring R X (f.left ⁻¹ᵁ Y.left.basicOpen r))
    simpa only [List.map_ofFn, Function.comp_def] using h
  have hnormal : Ideal.span (Set.range (IdealSheafPrincipalEquations.sequence U r a)) =
      RingHom.ker (f.left.app (Y.left.basicOpen r)).hom := by
    have h := IdealSheafPrincipalEquations.generates f.left.ker U hU r a ha
    simpa only [Scheme.Hom.ker_apply] using h
  let t' := CompositeSectionKernel.lift (f.left.app (Y.left.basicOpen r)).hom
    (f.left.app_surjective _ (hU.basicOpen r)) (quotientParameter R X Y f s hs U hsU σ e r)
  refine ⟨r, ⟨{ contains := hcontains, parameter := t', lift := ?_, kernel := ?_, regular := ?_ }⟩⟩
  · exact CompositeSectionKernel.lift_eq _ _ _
  · exact CompositeSectionKernel.lifted_kernel _ _ _ _ _ hnormal ht
  · exact CompositeSectionKernel.lifted_regular _ _ _ _ hnormal
      (IdealSheafPrincipalEquations.weaklyRegular U hU r a hareg) htreg

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.PointParameterNeighborhood
