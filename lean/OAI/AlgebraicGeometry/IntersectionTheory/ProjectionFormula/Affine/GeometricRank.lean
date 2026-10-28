import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SpectrumRank
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SupportSpectrum
import OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimensionDrop

/-! # Geometric Rank -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.GeometricRank

noncomputable section

/-! The affine transcendence rank equals the actual dimension of the
closure of the corresponding geometric point. Support containment in
the scheme therefore bounds every contracted stalk prime. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {K : Type} [Field K] {X : Scheme}

def support (U : X.affineOpens) (p : PrimeSpectrum Γ(X, U)) : IrreducibleCloseds X :=
  irreducibleSetEquivPoints.symm (U.2.fromSpec p)

theorem ideal (U : X.affineOpens) (p : PrimeSpectrum Γ(X, U)) :
    (CycleClass.Geometric.GenericPoint.reducedSupportIdeal (support U p)).ideal U = p.asIdeal := by
  change PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' closure ({U.2.fromSpec p} : Set X)) = _
  have he := U.2.fromSpec.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image ({p} : Set (Spec Γ(X, U)))
  rw [Set.image_singleton] at he
  rw [← he, PrimeSpectrum.vanishingIdeal_closure, PrimeSpectrum.vanishingIdeal_singleton]

theorem dimension (f : X ⟶ Spec (.of K)) (U : X.affineOpens) (p : PrimeSpectrum Γ(X, U)) :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
    SpectrumRank.dimension K Γ(X, U) p = Foundations.Scheme.SupportDimension.supportTranscendenceDimension (support U p) f := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let : Nonempty (Foundations.Scheme.SupportAffineQuotient.supportAffineOpen (support U p) U) :=
    (Foundations.Scheme.SupportAffineInclusion.supportAffineOpen_nonempty_iff (support U p) U).mpr ⟨U.2.fromSpec p,
      subset_closure (Set.mem_singleton _), U.2.range_fromSpec ▸ Set.mem_range_self p⟩
  rw [Foundations.Scheme.SupportDimension.supportTranscendenceDimension_eq_affineQuotient (support U p) f U]
  change (Algebra.trdeg K (Γ(X, U) ⧸ p.asIdeal)).toNat =
    (Algebra.trdeg K (Γ(X, U) ⧸ (CycleClass.Geometric.GenericPoint.reducedSupportIdeal (support U p)).ideal U)).toNat
  rw [GeometricRank.ideal]

theorem point_dimension (f : X ⟶ Spec (.of K)) (U : X.affineOpens) (x : X) (hx : x ∈ U.1) :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
    SpectrumRank.dimension K Γ(X, U) (U.2.primeIdealOf ⟨x, hx⟩) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f := by
  rw [dimension]
  simp only [support, U.2.fromSpec_primeIdealOf]

theorem stalk_image (U : X.affineOpens) (x : X) (hx : x ∈ U.1)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    U.2.fromSpec (PrimeSpectrum.comap (X.presheaf.germ U.1 x hx).hom p) = X.fromSpecStalk x p :=
  congrArg (fun g : Spec (X.presheaf.stalk x) ⟶ X => g p)
    (U.2.fromSpecStalk_eq_fromSpecStalk hx)

theorem support_le (U : X.affineOpens) (x : X) (hx : x ∈ U.1)
    (W : IrreducibleCloseds X) (p : PrimeSpectrum (X.presheaf.stalk x))
    (hp : X.fromSpecStalk x p ∈ (W : Set X)) :
    support U (PrimeSpectrum.comap (X.presheaf.germ U.1 x hx).hom p) ≤ W := by
  change closure ({U.2.fromSpec (PrimeSpectrum.comap (X.presheaf.germ U.1 x hx).hom p)} : Set X) ⊆ _
  rw [stalk_image]
  exact closure_minimal (Set.singleton_subset_iff.mpr hp) W.isClosed

theorem bound (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (U : X.affineOpens) (x : X) (hx : x ∈ U.1)
    (W : IrreducibleCloseds X) (p : PrimeSpectrum (X.presheaf.stalk x))
    (hp : X.fromSpecStalk x p ∈ (W : Set X)) :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
    SpectrumRank.dimension K Γ(X, U) (PrimeSpectrum.comap (X.presheaf.germ U.1 x hx).hom p) ≤
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f := by
  rw [dimension]
  exact (Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_strictMono f).monotone (support_le U x hx W p hp)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.GeometricRank
