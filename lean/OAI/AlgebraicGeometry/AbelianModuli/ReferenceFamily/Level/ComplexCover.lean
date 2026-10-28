import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Torsion
import OAI.AlgebraicGeometry.Foundations.Scheme.ComplexPointExistence
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Complex Cover -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.ComplexCover.LevelCover

/-! The full-level parameter covers every polarized family on a complex
base locally of finite type. A nonempty complement would contain a genuine
complex point, whose native torsion supplies the missing full level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.ComplexPointExistence

variable {S : Scheme.{0}} {g N L : ℕ} {δ : Fin g → ℕ}
  (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
  (p : S ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [NeZero L]

theorem complex_point_mem_fullFrame_image (q : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S) (x : Foundations.Scheme.ProjectiveSpace.complexBase) :
    q x ∈ Set.range (Frame.Locus.LevelCover.fullFrameScheme A.abelian p (N := L)).hom := by
  let β := Polarized.Torsion.polarizedComplexFullLevel (A.pullback q) L
  let f := Frame.Factorization.LevelCover.fullFrameOfRelativeLevel A.abelian p (Over.mk q) β
  exact ⟨f.left x, congrArg (fun h : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S => h x) f.w⟩

/-- Surjectivity on every component follows from the actual complex
torsion calculation; no connectedness or supplied fiber is required. -/
theorem polarizedFullFrame_surjective [LocallyOfFiniteType p] :
    Surjective (Frame.Locus.LevelCover.fullFrameScheme A.abelian p (N := L)).hom := by
  constructor
  intro s
  by_contra hs
  let U : S.Opens := ⟨(Set.range (Frame.Locus.LevelCover.fullFrameScheme A.abelian p (N := L)).hom)ᶜ,
    (CoverIs.LevelCover.fullFrame_image_isClopen A.abelian p (N := L)).1.isOpen_compl⟩
  let : Nonempty U := ⟨⟨s, hs⟩⟩
  let q := Classical.choice (Foundations.Scheme.ComplexPointExistence.nonempty_complexOverPoints (U.ι ≫ p))
  have h := complex_point_mem_fullFrame_image A p (L := L) (q.left ≫ U.ι) (default : Foundations.Scheme.ProjectiveSpace.complexBase)
  exact (q.left (default : Foundations.Scheme.ProjectiveSpace.complexBase)).property h

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.ComplexCover.LevelCover

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily

/-! Full-level covers on bases locally of finite type over a field with
a complex embedding. Complex points of every nonempty open are obtained
by surjective base change followed by the proved complex-point theorem. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.ComplexPointExistence

variable {K : Type} [Field K] (κ : K →+* ℂ)

include κ in
theorem Level.ComplexCover.nonempty_complex_test {S : Scheme.{0}} (p : S ⟶ Spec (.of K))
    [LocallyOfFiniteType p] [Nonempty S] : Nonempty (Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S) := by
  let b : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom κ)
  let : Surjective b := ⟨Function.surjective_to_subsingleton _⟩
  let f := pullback.fst p b
  let : Nonempty (pullback p b : Scheme) :=
    ⟨Classical.choose (f.surjective (Classical.choice (inferInstance : Nonempty S)))⟩
  let q := Classical.choice (Foundations.Scheme.ComplexPointExistence.nonempty_complexOverPoints (pullback.snd p b))
  exact ⟨q.left ≫ f⟩

namespace Level.ComplexCover.LevelCover

variable [CharZero K] {S : Scheme.{0}} {g N L : ℕ} {δ : Fin g → ℕ}
  (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
  (p : S ⟶ Spec (.of K)) [NeZero L]

include κ in
theorem polarizedFullFrame_surjective_of_locallyOfFiniteType [LocallyOfFiniteType p] :
    Surjective (Frame.Locus.LevelCover.fullFrameScheme A.abelian p (N := L)).hom := by
  constructor
  intro s
  by_contra hs
  let U : S.Opens := ⟨(Set.range (Frame.Locus.LevelCover.fullFrameScheme A.abelian p (N := L)).hom)ᶜ,
    (CoverIs.LevelCover.fullFrame_image_isClopen A.abelian p (N := L)).1.isOpen_compl⟩
  let : Nonempty U := ⟨⟨s, hs⟩⟩
  let q := Classical.choice (nonempty_complex_test κ (U.ι ≫ p))
  have h := Polarized.Torsion.LevelCover.polarized_point_mem_fullFrame_image A p (L := L) (q ≫ U.ι) (default : Foundations.Scheme.ProjectiveSpace.complexBase)
  exact (q (default : Foundations.Scheme.ProjectiveSpace.complexBase)).property h

end Level.ComplexCover.LevelCover

variable [NumberField K] {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] {s N L : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
  {T : Over (Spec (.of K))} (A : PEL.Objects.PELObject P iota N T) [NeZero L]

include κ in
theorem PEL.Objects.PELObject.auxiliaryLevelProjection_surjective_of_locallyOfFiniteType [LocallyOfFiniteType T.hom] :
    Surjective (PEL.Objects.PELObject.auxiliaryLevelProjection A (L := L)).left :=
  Level.ComplexCover.LevelCover.polarizedFullFrame_surjective_of_locallyOfFiniteType κ A.polarized T.hom

end AlgebraicGeometry.AbelianModuli.ReferenceFamily

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.ComplexCover.LevelCover

/-! A constructed covering of full levels stays a covering after
arbitrary scheme base change and transport by a group-scheme isomorphism.
The pulled-back marking is built with the actual pullback comparisons. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S T U : Scheme.{0}} {g N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {K : Type} [Field K] [CharZero K] (p : S ⟶ Spec (.of K)) [NeZero N]

theorem fullFrame_surjective_of_cover (u : U ⟶ S) [Surjective u]
    (β : (A.pullback u).FullLevel N) : Surjective (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).hom := by
  let f := Frame.Factorization.LevelCover.fullFrameOfRelativeLevel A p (Over.mk u) β
  constructor
  intro s
  obtain ⟨t, ht⟩ := u.surjective s
  exact ⟨f.left t, (congrArg (fun h : U ⟶ S => h t) f.w).trans ht⟩

/-- The level on a surjective cover pulls back through the actual
cartesian square, with the two composite base changes identified. -/
def levelOnBaseChangedCover (q : T ⟶ S) (u : U ⟶ S) (β : (A.pullback u).FullLevel N) :
    ((A.pullback q).pullback (pullback.snd u q)).FullLevel N := by
  let β₁ := (β.pullback (pullback.fst u q)).transport
    (A.pullbackCompIso u (pullback.fst u q)).symm
  let β₂ := β₁.transport
    (A.pullbackCongrIso (pullback.fst u q ≫ u) (pullback.snd u q ≫ q) pullback.condition)
  exact β₂.transport (A.pullbackCompIso q (pullback.snd u q))

/-- Full-level surjectivity persists over any test scheme, with no
finite-type hypothesis on the new base. -/
theorem fullFrame_surjective_pullback (q : T ⟶ S)
    [Surjective (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).hom] :
    Surjective (Frame.Locus.LevelCover.fullFrameScheme (A.pullback q) (q ≫ p) (N := N)).hom :=
  fullFrame_surjective_of_cover (A.pullback q) (q ≫ p)
    (pullback.snd (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).hom q)
      (levelOnBaseChangedCover A q (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).hom
        (Finite.Monomorphisms.LevelCover.canonicalFullFrameLevel A p))

theorem fullFrame_surjective_of_iso (B : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    [Surjective (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).hom] :
    Surjective (Frame.Locus.LevelCover.fullFrameScheme B p (N := N)).hom := by
  let u := (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).hom
  let : GrpObj ((Over.pullback u).obj A.scheme) := Functor.grpObjObj
  let : GrpObj ((Over.pullback u).obj B.scheme) := Functor.grpObjObj
  let e' : (A.pullback u).scheme ≅ (B.pullback u).scheme := (Over.pullback u).mapIso e
  let : IsMonHom e'.hom := by
    dsimp only [e', HilbertConstruction.Abelian.Schemes.AbelianScheme.pullback]
    exact inferInstanceAs (IsMonHom ((Over.pullback u).map e.hom))
  let β := (Finite.Monomorphisms.LevelCover.canonicalFullFrameLevel A p).transport e'
  exact fullFrame_surjective_of_cover B p u β

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.ComplexCover.LevelCover

end

end OAI
