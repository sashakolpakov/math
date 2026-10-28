import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResolutionOrientation
import OAI.NumberTheory.PadicHodge.IntegralComparison.LinearHomOrientedPurity

/-! # Conormal Koszul Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConormalKoszulPurity

noncomputable section

/-! Canonical oriented purity into the dual of the conormal determinant.
The map is independent of the regular generators and their matching basis. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResolutionOrientation
  Koszul.TopBoundary TopExteriorCoordinates

universe u
variable (R : Type u) [CommRing R] {n : ℕ} (I : Ideal R)
  (s : Fin n → R) (hs : Koszul.OrientedTopCohomology.ideal R s = I)

def conormalVectors (i : Fin n) : I :=
  ⟨s i, by rw [← hs]; exact Ideal.subset_span (Set.mem_range_self i)⟩

include hs in
theorem exists_change_matrix (t : Fin n → R) (ht : Koszul.OrientedTopCohomology.ideal R t = I) :
    ∃ A : Matrix (Fin n) (Fin n) R, ∀ i, s i = ∑ j, A i j * t j := by
  have hm (i : Fin n) : s i ∈ Ideal.span (Set.range t) := by
    rw [show Ideal.span (Set.range t) = I from ht, ← hs]
    exact Ideal.subset_span (Set.mem_range_self i)
  choose a ha using fun i => (Submodule.mem_span_range_iff_exists_fun R).mp (hm i)
  exact ⟨a, fun i => (ha i).symm⟩

def iso (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s))
    (P : ProjectiveResolution (ModuleCat.of R (R ⧸ I)))
    (b : Module.Basis (Fin n) (R ⧸ I) I.Cotangent) :
    (DualComplexHomology.complex R P.complex).homology n ≅
      ModuleCat.of R (Module.Dual (R ⧸ I) (⋀[R ⧸ I]^n I.Cotangent)) :=
  Koszul.ResolutionOrientation.purityIso R I s hs hreg P ≪≫ ((Koszul.TopBoundary.topDualEquiv (R ⧸ I) b).symm.restrictScalars R).toModuleIso

theorem topDualEquiv_change {Q V : Type u} [CommRing Q] [AddCommGroup V] [Module Q V]
    (b b' : Module.Basis (Fin n) Q V) (a : Module.Dual Q (⋀[Q]^n V)) :
    Koszul.TopBoundary.topDualEquiv Q b a = b'.det b * Koszul.TopBoundary.topDualEquiv Q b' a := by
  change a (TopExteriorCoordinates.generator b) = b'.det b * a (TopExteriorCoordinates.generator b')
  have h : TopExteriorCoordinates.generator b = b'.det b • TopExteriorCoordinates.generator b' :=
    TopExteriorDeterminant.alternating_apply_eq_det_smul b' (exteriorPower.ιMulti Q n) b
  rw [h, map_smul, smul_eq_mul]

variable (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s))
  (P : ProjectiveResolution (ModuleCat.of R (R ⧸ I)))
  (b : Module.Basis (Fin n) (R ⧸ I) I.Cotangent)
  (hb : ∀ i, b i = I.toCotangent (conormalVectors R I s hs i))
  (t : Fin n → R) (ht : Koszul.OrientedTopCohomology.ideal R t = I)
  (htreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn t))
  (bt : Module.Basis (Fin n) (R ⧸ I) I.Cotangent)
  (hbt : ∀ i, bt i = I.toCotangent (conormalVectors R I t ht i))

include hb hbt in
theorem independent_generators :
    iso R I s hs hreg P b = iso R I t ht htreg P bt := by
  obtain ⟨A, hA⟩ := exists_change_matrix R I s hs t ht
  have hd : bt.det b = Ideal.Quotient.mk I A.det := by
    have h := Koszul.GeneratorMatrix.conormal_determinant I
      (conormalVectors R I s hs) (conormalVectors R I t ht) bt hbt A hA
    simpa only [← hb] using h
  apply Iso.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (Koszul.TopBoundary.topDualEquiv (R ⧸ I) b).injective
  change Koszul.TopBoundary.topDualEquiv (R ⧸ I) b ((Koszul.TopBoundary.topDualEquiv (R ⧸ I) b).symm
    ((Koszul.ResolutionOrientation.purityIso R I s hs hreg P).hom x)) =
    Koszul.TopBoundary.topDualEquiv (R ⧸ I) b ((Koszul.TopBoundary.topDualEquiv (R ⧸ I) bt).symm
      ((Koszul.ResolutionOrientation.purityIso R I t ht htreg P).hom x))
  rw [LinearEquiv.apply_symm_apply, topDualEquiv_change b bt, LinearEquiv.apply_symm_apply, hd]
  have h := congrArg (fun f => f x)
    (Koszul.ResolutionOrientation.purity_transition R I s hs hreg t ht htreg A hA P)
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConormalKoszulPurity
