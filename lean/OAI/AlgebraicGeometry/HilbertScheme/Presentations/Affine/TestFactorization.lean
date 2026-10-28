import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.MorphismFactorization
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SubfunctorRepresentations

/-! # Test Factorization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.TestFactorization

noncomputable section

/-! A monomorphic parameter map represents a local geometric condition
on all test schemes as soon as it does so on affine test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {M Z : Over S}

theorem over_lift_of_openCover {T : Over S} (U : T.left.OpenCover.{u})
    (x : T ⟶ M) (j : Z ⟶ M) [Mono j.left]
    (h : ∀ i, ∃ g : Over.mk (U.f i ≫ T.hom) ⟶ Z,
      g ≫ j = (Over.homMk (U.f i) rfl : Over.mk (U.f i ≫ T.hom) ⟶ T) ≫ x) :
    ∃! g : T ⟶ Z, g ≫ j = x := by
  obtain ⟨g, hg, _⟩ := Local.MorphismFactorization.lift_of_openCover U x.left j.left (fun i => by
    obtain ⟨k, hk⟩ := h i
    exact ⟨k.left, congrArg Over.Hom.left hk⟩)
  have hw : g ≫ Z.hom = T.hom := by
    rw [← j.w, ← Category.assoc, hg]
    exact x.w
  let l : T ⟶ Z := Over.homMk g hw
  have hl : l ≫ j = x := Over.OverMorphism.ext hg
  let : Mono j := Over.mono_of_mono_left j
  exact ⟨l, hl, fun k hk => (cancel_mono j).mp (hk.trans hl.symm)⟩

theorem subfunctor_lifts_of_affine_tests (F : Subfunctor (yoneda.obj M))
    (j : Z ⟶ M) [Mono j.left]
    (hlocal : ∀ (T : Over S) (x : T ⟶ M),
      (∀ i : T.left.affineOpenCover.I₀,
        ((Over.homMk (T.left.affineOpenCover.f i) rfl :
          Over.mk (T.left.affineOpenCover.f i ≫ T.hom) ⟶ T) ≫ x) ∈
            F.obj (.op (Over.mk (T.left.affineOpenCover.f i ≫ T.hom)))) → x ∈ F.obj (.op T))
    (haff : ∀ (T : Over S) [IsAffine T.left] (x : T ⟶ M),
      x ∈ F.obj (.op T) ↔ ∃ y : T ⟶ Z, y ≫ j = x)
    (T : Over S) (x : T ⟶ M) :
    x ∈ F.obj (.op T) ↔ ∃! y : T ⟶ Z, y ≫ j = x := by
  let C := T.left.affineOpenCover
  let U (i : C.I₀) : Over S := Over.mk (C.f i ≫ T.hom)
  let b (i : C.I₀) : U i ⟶ T := Over.homMk (C.f i) rfl
  constructor
  · intro hx
    apply over_lift_of_openCover C.openCover x j
    intro i
    exact (@haff (U i) (inferInstanceAs (IsAffine (Spec (C.X i)))) (b i ≫ x)).mp (F.map (b i).op hx)
  · rintro ⟨y, hy, _⟩
    apply hlocal T x
    intro i
    apply (@haff (U i) (inferInstanceAs (IsAffine (Spec (C.X i)))) (b i ≫ x)).mpr
    exact ⟨b i ≫ y, (Category.assoc _ _ _).trans (congrArg (fun f => b i ≫ f) hy)⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.TestFactorization
