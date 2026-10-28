import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineRing
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupoidIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineSpanIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineKernelIs
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-! # Affine Groupoid Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineGroupoidIs.Construction.AffineGroupoid

/-!
# Invariants of actual affine equivalence relations

The composition squares proved in `Groupoid` give the two ring pushouts.
Their base-change bases supply the hypotheses of the invariant polynomial
calculation; those hypotheses are discharged for the relation, not assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.Module

universe u v

/-- Base change of a basis along a pushout of commutative rings. The algebra
structures are specified by the displayed maps. -/
theorem exists_basis_of_isPushout
    {R A S B : CommRingCat.{u}} {ι : Type v}
    (a : R ⟶ A) (s : R ⟶ S) (p : A ⟶ B) (q : S ⟶ B)
    (h : IsPushout a s p q)
    (b : letI := a.hom.toAlgebra; Basis ι R A) :
    letI := q.hom.toAlgebra
    ∃ d : Basis ι S B, ∀ i, d i = p (b i) := by
  let := a.hom.toAlgebra
  let := s.hom.toAlgebra
  let := p.hom.toAlgebra
  let := q.hom.toAlgebra
  let := (q.hom.comp s.hom).toAlgebra
  have : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r =>
    congrArg (fun f : R ⟶ B => f r) h.w.symm
  have hpush : Algebra.IsPushout R S A B :=
    CommRingCat.isPushout_iff_isPushout.mp h.flip
  refine ⟨hpush.out.basis b, ?_⟩
  intro i
  exact hpush.out.basis_apply b i

/-- Coordinate identities and the two bases obtained from the composition
squares. These are data of the original relation, before constructing a quotient. -/
structure CompositionBases
    {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra B D] {ι : Type v}
    (t : A →+* B) (p c : B →+* D) (b : Basis ι A B) where
  target_injective : Function.Injective t
  second_source : ∀ a, p (algebraMap A B a) = algebraMap B D (t a)
  compose_source : ∀ a, c (algebraMap A B a) = algebraMap B D (algebraMap A B a)
  compose_target : ∀ a, c (t a) = p (t a)
  secondBasis : Basis ι B D
  composeBasis : Basis ι B D
  secondBasis_apply : ∀ i, secondBasis i = p (b i)
  composeBasis_apply : ∀ i, composeBasis i = c (b i)

/-- The two bases and compatibility identities come from the affine
equivalence relation itself. -/
noncomputable def compositionBases
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (s t : V ⟶ U) (e : CategoryTheory.EquivalenceRelation s t)
    {ι : Type v}
    (b : letI := s.appTop.hom.toAlgebra; Basis ι Γ(U, ⊤) Γ(V, ⊤)) :
    letI := s.appTop.hom.toAlgebra
    letI := e.c.fst.appTop.hom.toAlgebra
    CompositionBases t.appTop.hom e.c.snd.appTop.hom e.t.appTop.hom b := by
  apply Classical.choice
  let A := Γ(U, ⊤)
  let B := Γ(V, ⊤)
  let D := Γ(e.c.pt, ⊤)
  let : Algebra A B := s.appTop.hom.toAlgebra
  let : Algebra B D := e.c.fst.appTop.hom.toAlgebra
  have hpb : IsPullback e.c.fst e.c.snd t s := IsPullback.of_isLimit e.isLimit
  obtain ⟨dp, hdp⟩ := exists_basis_of_isPushout
    s.appTop t.appTop e.c.snd.appTop e.c.fst.appTop
    (isPushout_appTop_of_isPullback hpb).flip b
  obtain ⟨dc, hdc⟩ := exists_basis_of_isPushout
    s.appTop s.appTop e.t.appTop e.c.fst.appTop
    (isPushout_appTop_of_isPullback (GroupoidIs.Construction.Groupoid.composition_source_isPullback e)) b
  have ht : Function.Injective t.appTop.hom := by
    apply Function.LeftInverse.injective (g := e.r.appTop.hom)
    intro r
    have h := congrArg (fun f : U ⟶ U => f.appTop r) e.reflexivity₂
    simpa only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop,
      CommRingCat.comp_apply, CommRingCat.id_apply] using h
  have hp : ∀ r, e.c.snd.appTop.hom (algebraMap A B r) =
      algebraMap B D (t.appTop.hom r) := by
    intro r
    change e.c.snd.appTop (s.appTop r) = e.c.fst.appTop (t.appTop r)
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
      congrArg (fun f : e.c.pt ⟶ U => f.appTop r) e.c.condition.symm
  have hc : ∀ r, e.t.appTop.hom (algebraMap A B r) =
      algebraMap B D (algebraMap A B r) := by
    intro r
    change e.t.appTop (s.appTop r) = e.c.fst.appTop (s.appTop r)
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
      congrArg (fun f : e.c.pt ⟶ U => f.appTop r) e.transitivity₁
  have hct : ∀ r, e.t.appTop.hom (t.appTop.hom r) =
      e.c.snd.appTop.hom (t.appTop.hom r) := by
    intro r
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
      congrArg (fun f : e.c.pt ⟶ U => f.appTop r) e.transitivity₂
  exact ⟨⟨ht, hp, hc, hct, dp, dc, hdp, hdc⟩⟩

/-- Every element of the affine object ring is integral over the relation
invariants when the source ring extension has a finite basis. -/
theorem integral_of_affine_equivalence_relation
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (s t : V ⟶ U) (e : CategoryTheory.EquivalenceRelation s t)
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (b : letI := s.appTop.hom.toAlgebra; Basis ι Γ(U, ⊤) Γ(V, ⊤))
    (a : Γ(U, ⊤)) :
    let C := s.appTop.hom.eqLocus t.appTop.hom
    letI : Algebra C Γ(U, ⊤) := C.subtype.toAlgebra
    IsIntegral C a := by
  let := s.appTop.hom.toAlgebra
  let := e.c.fst.appTop.hom.toAlgebra
  let d := compositionBases s t e b
  exact InvariantPolynomialOf.Construction.InvariantPolynomial.integral_over_invariants t.appTop.hom d.target_injective
    e.c.snd.appTop.hom e.t.appTop.hom d.second_source d.compose_source d.compose_target
    b d.secondBasis d.composeBasis d.secondBasis_apply d.composeBasis_apply a

/-- The invariant-ring quotient projection of a finite-free affine equivalence
relation is integral and surjective. -/
theorem quotient_projection_integral_surjective
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (s t : V ⟶ U) (e : CategoryTheory.EquivalenceRelation s t)
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (b : letI := s.appTop.hom.toAlgebra; Basis ι Γ(U, ⊤) Γ(V, ⊤)) :
    IsIntegralHom (AffineRing.Construction.Affine.projection s.appTop.hom t.appTop.hom) ∧
      Surjective (AffineRing.Construction.Affine.projection s.appTop.hom t.appTop.hom) := by
  let C := s.appTop.hom.eqLocus t.appTop.hom
  let : Algebra C Γ(U, ⊤) := C.subtype.toAlgebra
  have h : Algebra.IsIntegral C Γ(U, ⊤) :=
    ⟨integral_of_affine_equivalence_relation s t e b⟩
  have hi : C.subtype.IsIntegral := algebraMap_isIntegral_iff.mpr h
  refine ⟨IsIntegralHom.SpecMap_iff.mpr hi, ?_⟩
  exact ⟨hi.comap_surjective Subtype.val_injective⟩

/-- The invariant-spectrum projection of a closed affine equivalence relation
with finite-free source is finite, flat, finitely presented and surjective. -/
theorem quotient_projection_finiteLocallyFree_surjective
    {U V S : Scheme.{u}} [IsAffine U] [IsAffine V] [IsAffine S]
    (a : U ⟶ S) (s t : V ⟶ U) (e : CategoryTheory.EquivalenceRelation s t)
    (h : s ≫ a = t ≫ a) [IsClosedImmersion (pullback.lift s t h)]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (b : letI := s.appTop.hom.toAlgebra; Basis ι Γ(U, ⊤) Γ(V, ⊤)) :
    IsFinite (AffineRing.Construction.Affine.projection s.appTop.hom t.appTop.hom) ∧
      Flat (AffineRing.Construction.Affine.projection s.appTop.hom t.appTop.hom) ∧
      LocallyOfFinitePresentation (AffineRing.Construction.Affine.projection s.appTop.hom t.appTop.hom) ∧
      Surjective (AffineRing.Construction.Affine.projection s.appTop.hom t.appTop.hom) := by
  let := s.appTop.hom.toAlgebra
  let := e.c.fst.appTop.hom.toAlgebra
  let d := compositionBases s t e b
  have hspan := AffineSpanIs.Construction.AffineSpan.span_of_closedImmersion a s t h
  obtain ⟨hfinite, hflat, hfp⟩ := FlatInvariants.Construction.FiniteFlatInvariants.finite_flat_finitelyPresented
    t.appTop.hom d.target_injective e.c.snd.appTop.hom e.t.appTop.hom
    d.second_source d.compose_source d.compose_target b d.secondBasis d.composeBasis
    d.secondBasis_apply d.composeBasis_apply hspan
  refine ⟨(IsFinite.SpecMap_iff _).mpr hfinite, Flat.SpecMap_iff.mpr hflat,
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr hfp, ?_⟩
  exact (quotient_projection_integral_surjective s t e b).2

/-- The original affine equivalence relation is the scheme-theoretic kernel
pair of the invariant-spectrum quotient projection. -/
theorem quotient_projection_isKernelPair
    {U V S : Scheme.{u}} [IsAffine U] [IsAffine V] [IsAffine S]
    (a : U ⟶ S) (s t : V ⟶ U) (e : CategoryTheory.EquivalenceRelation s t)
    (h : s ≫ a = t ≫ a) [IsClosedImmersion (pullback.lift s t h)]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (b : letI := s.appTop.hom.toAlgebra; Basis ι Γ(U, ⊤) Γ(V, ⊤)) :
    IsKernelPair (AffineRing.Construction.Affine.projection s.appTop.hom t.appTop.hom)
      (Spec.map (CommRingCat.ofHom s.appTop.hom))
      (Spec.map (CommRingCat.ofHom t.appTop.hom)) := by
  let := s.appTop.hom.toAlgebra
  let := e.c.fst.appTop.hom.toAlgebra
  let d := compositionBases s t e b
  obtain ⟨e₀, he₀⟩ := InvariantTensorExists.Construction.InvariantTensor.exists_tensor_equiv t.appTop.hom d.target_injective
    e.c.snd.appTop.hom e.t.appTop.hom d.second_source d.compose_source d.compose_target
    b d.secondBasis d.composeBasis d.secondBasis_apply d.composeBasis_apply
    (AffineSpanIs.Construction.AffineSpan.span_of_closedImmersion a s t h)
  exact AffineKernelIs.Construction.AffineKernel.projection_isKernelPair_of_tensor_equiv t.appTop.hom e₀ he₀

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineGroupoidIs.Construction.AffineGroupoid
