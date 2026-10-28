import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Characters
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! # Character Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes

noncomputable section

/-!
# CartierDuality: the actual fppf character sheaf

The multiplicative group is obtained from its integral Hopf-algebra model.
The character sheaf is the internal Hom of group-valued functors of points.
Neither definition includes representability or perfect-duality assumptions.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u

/-- The multiplicative group over an arbitrary scheme. -/
def multiplicativeGroupOver (S : Scheme.{u}) : Grp (Over S) :=
  (Over.pullback (specULiftZIsTerminal.from S)).mapGrp.obj
    (Characters.Construction.multiplicativeGroupScheme (ULift.{u} ℤ))

/-- The group-valued functor of points satisfies fppf descent. -/
theorem groupPoints_isSheaf (S : Scheme.{u}) (G : Grp (Over S)) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (yonedaGrp.obj G) := by
  apply Presheaf.isSheaf_of_isSheaf_comp (Scheme.fppfTopology.over S)
    (yonedaGrp.obj G) (forget GrpCat)
  let : (yonedaGrp.obj G ⋙ forget GrpCat).IsRepresentable :=
    ⟨G.X, ⟨yonedaGrpObjRepresentableBy G.X⟩⟩
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- The fppf character functor, with values in the universe of natural
transformations on the big site. -/
def characterSheaf (S : Scheme.{u}) (G : Grp (Over S)) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨presheafHom (yonedaGrp.obj G) (yonedaGrp.obj (multiplicativeGroupOver S)),
    Presheaf.IsSheaf.hom (F := yonedaGrp.obj G)
      (G := yonedaGrp.obj (multiplicativeGroupOver S))
      (groupPoints_isSheaf S (multiplicativeGroupOver S))⟩

/-- A section over T is a natural group homomorphism on all schemes over T. -/
theorem characterSheaf_sections (S : Scheme.{u}) (G : Grp (Over S)) (T : Over S) :
    (characterSheaf S G).obj.obj (Opposite.op T) =
      ((Over.forget T).op ⋙ yonedaGrp.obj G ⟶
        (Over.forget T).op ⋙ yonedaGrp.obj (multiplicativeGroupOver S)) := rfl

/-- The trivial natural group homomorphism. -/
def trivialGroupNatTrans {C : Type*} [Category* C] (F G : C ⥤ GrpCat.{u}) : F ⟶ G where
  app X := GrpCat.ofHom (1 : F.obj X →* G.obj X)
  naturality := by intro X Y f; ext x; simp

/-- Restriction of characters along a group-scheme homomorphism. -/
def characterRestriction {S : Scheme.{u}} {H G : Grp (Over S)} (i : H ⟶ G) :
    characterSheaf S G ⟶ characterSheaf S H :=
  ⟨{
    app T := ↾(fun χ =>
      Functor.whiskerLeft (Over.forget T.unop).op (yonedaGrp.map i) ≫ χ)
    naturality := by intro X Y f; ext χ; rfl
  }⟩

/-- The constant map to the trivial character, in the same codomain as
the restriction map. -/
def characterTrivialRestriction {S : Scheme.{u}} (G H : Grp (Over S)) :
    characterSheaf S G ⟶ characterSheaf S H :=
  ⟨{
    app T := ↾(fun _ => trivialGroupNatTrans
      ((Over.forget T.unop).op ⋙ yonedaGrp.obj H)
      ((Over.forget T.unop).op ⋙ yonedaGrp.obj (multiplicativeGroupOver S)))
    naturality := by intro X Y f; ext χ; rfl
  }⟩

/-- The sheaf of characters trivial on H. This is the actual equalizer,
defined before any assertion of finite locally free representability. -/
def annihilatorSheaf {S : Scheme.{u}} {H G : Grp (Over S)} (i : H ⟶ G) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  equalizer (characterRestriction i) (characterTrivialRestriction G H)

/-- A character-valued morphism factors uniquely through the annihilator
precisely when its restriction is trivial. -/
theorem annihilatorSheaf_universal_property
    {S : Scheme.{u}} {H G : Grp (Over S)} (i : H ⟶ G)
    (F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))
    (f : F ⟶ characterSheaf S G)
    (hf : f ≫ characterRestriction i = f ≫ characterTrivialRestriction G H) :
    ∃! g : F ⟶ annihilatorSheaf i,
      g ≫ equalizer.ι (characterRestriction i) (characterTrivialRestriction G H) = f := by
  refine ⟨equalizer.lift f hf, equalizer.lift_ι f hf, ?_⟩
  intro g hg
  apply equalizer.hom_ext
  exact hg.trans (equalizer.lift_ι f hf).symm

/-- Restriction to the site over any test scheme preserves equalizers. -/
instance slicePullback_preservesEqualizers (S : Scheme.{u}) (T : Over S) :
    PreservesLimitsOfShape WalkingParallelPair
      ((Scheme.fppfTopology.over S).overPullback (Type (u + 1)) T) where
  preservesLimit := by
    intro K
    let J := Scheme.fppfTopology.over S
    let F := J.overPullback (Type (u + 1)) T
    have : PreservesLimitsOfShape WalkingParallelPair
        (F ⋙ sheafToPresheaf (J.over T) (Type (u + 1))) :=
      preservesLimitsOfShape_of_natIso
        ((Over.forget T).sheafPushforwardContinuousCompSheafToPresheafIso
          (Type (u + 1)) (J.over T) J).symm
    exact preservesLimit_of_reflects_of_preserves F
      (sheafToPresheaf (J.over T) (Type (u + 1)))

/-- The annihilator construction commutes with restriction to every
relative test site, including those obtained from special fibers. -/
def annihilatorSheaf_sliceIso
    {S : Scheme.{u}} {H G : Grp (Over S)} (i : H ⟶ G) (T : Over S) :
    ((Scheme.fppfTopology.over S).overPullback (Type (u + 1)) T).obj
      (annihilatorSheaf i) ≅
    equalizer
      (((Scheme.fppfTopology.over S).overPullback (Type (u + 1)) T).map
        (characterRestriction i))
      (((Scheme.fppfTopology.over S).overPullback (Type (u + 1)) T).map
        (characterTrivialRestriction G H)) :=
  PreservesEqualizer.iso _ _ _

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes
