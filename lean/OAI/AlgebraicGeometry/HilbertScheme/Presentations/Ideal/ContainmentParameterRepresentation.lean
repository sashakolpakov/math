import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ContainmentParameterFunctor
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SpectrumTestFactorization

/-! # Containment Parameter Representation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ContainmentParameterRepresentation.Hilbert

noncomputable section

/-! A closed-ambient parameter condition is represented on all test
schemes once its representing monomorphism is verified on spectra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (X : Over S) {B Z : Over S}
variable (I J : (Hilbert.Functor.ambient X B).IdealSheafData) (j : Z ⟶ B) [Mono j.left]
variable (hspec : ∀ (A : Type u) [CommRing A] (a : Spec (CommRingCat.of A) ⟶ S)
  (x : Over.mk a ⟶ B), x ∈ (ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor X I J).obj (.op (Over.mk a)) ↔
    ∃ y : Over.mk a ⟶ Z, y ≫ j = x)

include hspec in
theorem idealContainmentParameter_lifts (T : Over S) (x : T ⟶ B) :
    x ∈ (ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor X I J).obj (.op T) ↔
      ∃! y : T ⟶ Z, y ≫ j = x := by
  apply Affine.TestFactorization.subfunctor_lifts_of_affine_tests (ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor X I J) j ?_ ?_ T x
  · intro T x h
    let C := T.left.affineOpenCover
    let U (i : C.I₀) : Over S := Over.mk (C.f i ≫ T.hom)
    let f (i : C.I₀) : U i ⟶ T := Over.homMk (C.f i) rfl
    let : ∀ i, IsOpenImmersion (f i).left := fun i => inferInstanceAs (IsOpenImmersion (C.f i))
    exact ContainmentParameterFunctor.Hilbert.idealContainmentParameter_of_openCover X I J U f (fun t => C.openCover.exists_eq t) x h
  · intro T _ x
    exact SpectrumTestFactorization.affine_lifts_of_spectrum_tests (ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor X I J) j hspec T x

include hspec in
theorem idealContainmentParameter_representation :
    ∃ e : yoneda.obj Z ≅ (ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor X I J).toFunctor,
      e.hom ≫ (ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor X I J).ι = yoneda.map j := by
  let : Mono j := Over.mono_of_mono_left j
  apply SubfunctorRepresentations.subfunctor_representation_of_lifts (ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor X I J) j
  intro T x
  constructor
  · intro hx
    exact ((idealContainmentParameter_lifts X I J j hspec T x).mp hx).exists
  · rintro ⟨y, hy⟩
    exact (idealContainmentParameter_lifts X I J j hspec T x).mpr
      ⟨y, hy, fun z hz => (cancel_mono j).mp (hz.trans hy.symm)⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ContainmentParameterRepresentation.Hilbert
