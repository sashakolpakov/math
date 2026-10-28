import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitFrameTransport
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicPELMaps
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELTransport

/-! # PEL Frame Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric.PELFrameTransport

noncomputable section

/-! Full integral Tate images and actual isogeny preimage lattices
are preserved by complete PEL source and target isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {R : Type} [CommRing R] {g N s q n : ℕ} [Fact q.Prime]
    {S : Scheme} (T : Over S) {A A' B B' : AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData R g N S}

theorem pelTateIso_preserves_integral (a : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso A B)
    (u : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateModule A.abelian.scheme T q) (hu : u ∈ AlgebraicGeometry.AbelianScheme.TateComparison.Rational.integralTateImage A.abelian.scheme T q) :
    a.rationalTateEquiv T u ∈ AlgebraicGeometry.AbelianScheme.TateComparison.Rational.integralTateImage B.abelian.scheme T q := by
  obtain ⟨v, rfl⟩ := hu
  exact ⟨AlgebraicGeometry.AbelianScheme.TateComparison.Add.schemeTateMap A.abelian.scheme T q a.abelian.hom v, rfl⟩

theorem pelTateIso_integral_iff (a : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso A B) (u : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateModule A.abelian.scheme T q) :
    a.rationalTateEquiv T u ∈ AlgebraicGeometry.AbelianScheme.TateComparison.Rational.integralTateImage B.abelian.scheme T q ↔
      u ∈ AlgebraicGeometry.AbelianScheme.TateComparison.Rational.integralTateImage A.abelian.scheme T q := by
  constructor
  · intro hu
    have h := pelTateIso_preserves_integral T a.symm (a.rationalTateEquiv T u) hu
    change (a.rationalTateEquiv T).symm (a.rationalTateEquiv T u) ∈ _ at h
    rwa [LinearEquiv.symm_apply_apply] at h
  · exact pelTateIso_preserves_integral T a u

theorem pelFrameTransport_integral (a : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso A B)
    (frame : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateFrame s B.abelian.scheme T q) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedIntegralTateImage (a.transportFrame T frame) = AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedIntegralTateImage frame := by
  ext x
  constructor
  · rintro ⟨u, hu, he⟩
    exact ⟨a.rationalTateEquiv T u, pelTateIso_preserves_integral T a u hu, he⟩
  · rintro ⟨u, hu, he⟩
    refine ⟨(a.rationalTateEquiv T).symm u, ?_, ?_⟩
    · apply (pelTateIso_integral_iff T a _).mp
      rwa [LinearEquiv.apply_symm_apply]
    · change frame (a.rationalTateEquiv T ((a.rationalTateEquiv T).symm u)) = x
      rwa [LinearEquiv.apply_symm_apply]

theorem pelIsogeny_transport_tate (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A B n)
    (a : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso A' A) (b : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso B B')
    (u : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateModule A'.abelian.scheme T q) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateMap (T := T) (q := q) (e.transport a b).isogeny.hom u =
      b.rationalTateEquiv T (AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateMap (T := T) (q := q) e.isogeny.hom (a.rationalTateEquiv T u)) := by
  have h := AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicPELMaps.rationalTateMap_congr (T := T) (q := q)
    (e.transport a b).isogeny.hom (a.abelian.hom ≫ e.isogeny.hom ≫ b.abelian.hom) (e.transport_hom a b)
  rw [h, AlgebraicGeometry.AbelianScheme.TateComparison.Functor.rationalTateMap_comp, AlgebraicGeometry.AbelianScheme.TateComparison.Functor.rationalTateMap_comp]
  rfl

theorem pelIsogeny_transport_preimage_mem (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A B n)
    (a : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso A' A) (b : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso B B')
    (u : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateModule A'.abelian.scheme T q) :
    u ∈ AlgebraicGeometry.AbelianScheme.TateComparison.Rational.isogenyTatePreimage (T := T) (q := q) (e.transport a b).isogeny.hom ↔
      a.rationalTateEquiv T u ∈ AlgebraicGeometry.AbelianScheme.TateComparison.Rational.isogenyTatePreimage (T := T) (q := q) e.isogeny.hom := by
  change AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateMap (T := T) (q := q) (e.transport a b).isogeny.hom u ∈
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.integralTateImage B'.abelian.scheme T q ↔ _
  rw [pelIsogeny_transport_tate T e a b u, pelTateIso_integral_iff T b]
  rfl

theorem pelIsogeny_transport_framed_preimage (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A B n)
    (a : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso A' A) (b : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso B B') (frame : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateFrame s A.abelian.scheme T q) :
    (AlgebraicGeometry.AbelianScheme.TateComparison.Rational.isogenyTatePreimage (T := T) (q := q) (e.transport a b).isogeny.hom).map
        ((a.transportFrame T frame).toLinearMap.restrictScalars ℤ_[q]) =
      (AlgebraicGeometry.AbelianScheme.TateComparison.Rational.isogenyTatePreimage (T := T) (q := q) e.isogeny.hom).map
        (frame.toLinearMap.restrictScalars ℤ_[q]) := by
  ext x
  constructor
  · rintro ⟨u, hu, he⟩
    exact ⟨a.rationalTateEquiv T u, (pelIsogeny_transport_preimage_mem T e a b u).mp hu, he⟩
  · rintro ⟨u, hu, he⟩
    refine ⟨(a.rationalTateEquiv T).symm u, ?_, ?_⟩
    · apply (pelIsogeny_transport_preimage_mem T e a b _).mpr
      rwa [LinearEquiv.apply_symm_apply]
    · change frame (a.rationalTateEquiv T ((a.rationalTateEquiv T).symm u)) = x
      rwa [LinearEquiv.apply_symm_apply]

theorem pelIsogeny_transport_framed_lattice (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A B n)
    (a : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso A' A) (b : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso B B') (frame : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateFrame s A.abelian.scheme T q)
    (v : Fin s × Bool) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice (a.transportFrame T frame) (e.transport a b).isogeny.hom v =
      AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice frame e.isogeny.hom v := by
  rw [AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice, AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice, pelIsogeny_transport_framed_preimage T e a b frame]

end

end OAI.RepresentationTheory.Theta.Geometric.PELFrameTransport
