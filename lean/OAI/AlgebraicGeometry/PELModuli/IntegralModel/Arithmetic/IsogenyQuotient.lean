import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.IsogenyKernel
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.MultiplicationQuotient

/-! # Isogeny Quotient -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.IsogenyQuotient

noncomputable section

/-! Construct the arithmetic quotient by the descended complex isogeny
kernel. The quotient scheme, group law, geometric properties and exact
kernel on every test scheme come from the proved finite-group quotient.
The complex target identification is a subsequent quotient-uniqueness step. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
  (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
  {C : Over (Spec (.of ℂ))} [GrpObj C]
  (f : (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj A ⟶ C) [IsMonHom f]

/-- Actual arithmetic quotient data, constructed below from the complex
isogeny. The kernel comparison retains all scheme-theoretic test points. -/
structure ArithmeticIsogenyQuotient where
  baseExtension : Base.ArithmeticBaseExtension K κ
  target : Quotients.FiniteDescent.AbelianQuotient.Construction.AbelianScheme (Spec (.of baseExtension.extension.carrier))
  quotient : (Over.pullback baseExtension.fieldExtension).obj A ⟶ target.toOver
  [quotientGroup : IsMonHom quotient]
  finite : IsFinite quotient.left
  flat : Flat quotient.left
  finitePresentation : LocallyOfFinitePresentation quotient.left
  surjective : Surjective quotient.left
  subgroup : Over (Spec (.of baseExtension.extension.carrier))
  [subgroupGroup : GrpObj subgroup]
  subgroupFinite : IsFinite subgroup.hom
  subgroupEtale : Etale subgroup.hom
  inclusion : subgroup ⟶ (Over.pullback baseExtension.fieldExtension).obj A
  [inclusionGroup : IsMonHom inclusion]
  inclusionClosed : IsClosedImmersion inclusion.left
  complexKernelIso : Picard.PoincareBundle.Kernel.Scheme.kernelObject f ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom baseExtension.embedding))).obj subgroup
  [complexKernelGroup : IsMonHom complexKernelIso.hom]
  kernelComparison : complexKernelIso.hom.left ≫
    pullback.fst subgroup.hom (Spec.map (CommRingCat.ofHom baseExtension.embedding)) ≫
      inclusion.left ≫ pullback.fst A.hom baseExtension.fieldExtension =
        (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f).left ≫ pullback.fst A.hom (Spec.map (CommRingCat.ofHom κ))
  kernel : ∀ (T : Over (Spec (.of baseExtension.extension.carrier)))
    (a : T ⟶ (Over.pullback baseExtension.fieldExtension).obj A),
    a ≫ quotient = 1 ↔ ∃ h : T ⟶ subgroup, h ≫ inclusion = a

attribute [instance] ArithmeticIsogenyQuotient.quotientGroup ArithmeticIsogenyQuotient.subgroupGroup
  ArithmeticIsogenyQuotient.inclusionGroup ArithmeticIsogenyQuotient.complexKernelGroup

variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  [IsFinite f.left] [Etale f.left]

/-- Construct the smooth proper geometrically connected arithmetic
quotient by the actual descended isogeny kernel. -/
theorem arithmetic_isogeny_quotient_exists (N : ℕ) (hN : N ≠ 0) :
    ∃ D : ArithmeticIsogenyQuotient κ A f, D.baseExtension.denominator = N := by
  obtain ⟨B, hBN, G, hG, hFin, j, q, γ, hj, hjClosed, hγ, hHFinite, hHEtale, hγq, _, hcompare⟩ :=
    IsogenyKernel.finite_etale_isogeny_kernel_descends κ A f N hN
  let := hj
  let := hγ
  let H := AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G
  let A₀ : Quotients.FiniteDescent.AbelianQuotient.Construction.AbelianScheme (Spec (.of B.extension.carrier)) := {
    toOver := (Over.pullback B.fieldExtension).obj A
    proper := inferInstanceAs (IsProper (pullback.snd A.hom B.fieldExtension))
    smooth := inferInstanceAs (Smooth (pullback.snd A.hom B.fieldExtension))
    connected := inferInstanceAs (GeometricallyConnected (pullback.snd A.hom B.fieldExtension)) }
  have : Smooth A₀.toOver.hom := A₀.smooth
  have : IsProper A₀.toOver.hom := A₀.proper
  have : GeometricallyConnected A₀.toOver.hom := A₀.connected
  have : Etale H.hom := hHEtale
  have hH : Quotients.FiniteDescent.AbelianQuotient.Construction.FiniteLocallyFree H.hom := ⟨hHFinite, inferInstance, inferInstance⟩
  obtain ⟨Y, π, hπ, hπFree, hπSurj, hkernel, _⟩ :=
    Quotients.FiniteDescent.MultiplicationQuotient.Construction.exists_abelian_scheme_quotient_of_finite_multiplication
      (Spec (.of B.extension.carrier)) A₀ H j hjClosed hH
      (fun n hn => (IsogenyComplementGeometry.positive_multiplication_finite_etale_surjective A₀.toOver n hn).1)
  let D : ArithmeticIsogenyQuotient κ A f := {
    baseExtension := B
    target := Y
    quotient := π
    quotientGroup := hπ
    finite := hπFree.1
    flat := hπFree.2.1
    finitePresentation := hπFree.2.2
    surjective := hπSurj
    subgroup := H
    subgroupFinite := hHFinite
    subgroupEtale := hHEtale
    inclusion := j
    inclusionClosed := hjClosed
    complexKernelIso := γ
    kernelComparison := by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun a => a ≫ j.left ≫ pullback.fst A.hom B.fieldExtension) hγq).trans hcompare)
    kernel := by
      intro T a
      constructor
      · intro ha
        obtain ⟨h, hh, _⟩ := (hkernel T a).mp ha
        exact ⟨h, hh⟩
      · rintro ⟨h, hh⟩
        have : IsClosedImmersion j.left := hjClosed
        have : Mono j := Over.mono_of_mono_left j
        exact (hkernel T a).mpr ⟨h, hh, fun g hg => (cancel_mono j).mp (hg.trans hh.symm)⟩ }
  exact ⟨D, hBN⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.IsogenyQuotient
