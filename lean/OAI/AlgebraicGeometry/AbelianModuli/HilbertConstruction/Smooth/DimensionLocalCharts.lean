import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.SmoothDimensionOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.RelativeDimensionUniqueness

/-! # Dimension Local Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.DimensionLocalCharts

noncomputable section

/-! Every point of a smooth morphism has a source-open neighborhood of some fixed smooth relative dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem standardSmooth_exists_relativeDimension {R B : Type u} [CommRing R] [CommRing B]
    (f : R →+* B) (hf : f.IsStandardSmooth) : ∃ n, f.IsStandardSmoothOfRelativeDimension n := by
  let : Algebra R B := f.toAlgebra
  let : Algebra.IsStandardSmooth R B := hf
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := (inferInstance : Algebra.IsStandardSmooth R B).out
  let : Finite σ := hσ
  let : Finite ι := hι
  exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩

theorem smoothDimension_resLE_of_standardSmooth {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    {U : S.Opens} {V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) (hf : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n) :
    SmoothOfRelativeDimension n (f.resLE U V e) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]
  let Q : ∀ {R B : Type u} [CommRing R] [CommRing B], (R →+* B) → Prop :=
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
  have : (RingHom.toMorphismProperty Q).RespectsIso := RingHom.toMorphismProperty_respectsIso_iff.mp
    (RingHom.locally_respectsIso (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)))
  exact (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty Q) (arrowResLEAppIso f U V e)).mpr
    (RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)) _ hf)

theorem smooth_exists_sourceOpen_relativeDimension {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (x : X) :
    ∃ (n : ℕ) (V : X.Opens), x ∈ V ∧ SmoothOfRelativeDimension n (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := (Smooth.iff_forall_exists_isStandardSmooth f).mp inferInstance x
  obtain ⟨n, hn⟩ := standardSmooth_exists_relativeDimension _ hf
  have : SmoothOfRelativeDimension n (f.resLE U V e) := smoothDimension_resLE_of_standardSmooth f n hU hV e hn
  have hc : SmoothOfRelativeDimension (n + 0) (f.resLE U V e ≫ U.ι) :=
    smoothOfRelativeDimension_comp n 0 _ _
  rw [Nat.add_zero, Scheme.Hom.resLE_comp_ι] at hc
  exact ⟨n, V, hx, hc⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.DimensionLocalCharts
