import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CommutativeSheavesAb
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafEvaluation
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Evaluation

/-! # Sheaf Character Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality

noncomputable section

/-!
# CartierDuality: comparing native characters with characters in the common sheaf universe
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace SheafCharacterComparison.Construction.CommutativeSheaves

variable {C : Type (u + 1)} [Category.{u} C]

/-- Lifting the values of source and target groups preserves the actual
natural group homomorphisms defining a character section. -/
def uliftInternalHomMulEquiv (F : Cᵒᵖ ⥤ GrpCat.{u}) (K : Cᵒᵖ ⥤ CommGrpCat.{u}) (T : Cᵒᵖ) :
    (CommutativeSheavesAb.Construction.CommutativeSheaves.internalHom F K).obj T ≃*
      (CommutativeSheavesAb.Construction.CommutativeSheaves.internalHom (F ⋙ GrpCat.uliftFunctor.{u + 1, u})
        (K ⋙ CommGrpCat.uliftFunctor.{u + 1, u})).obj T where
  toEquiv := ((show GrpCat.uliftFunctor.{u + 1, u}.FullyFaithful from
    GrpCat.uliftFunctorFullyFaithful).whiskeringRight
    (Over T.unop)ᵒᵖ).homEquiv
      (X := (Over.forget T.unop).op ⋙ F)
      (Y := (Over.forget T.unop).op ⋙ K ⋙ forget₂ CommGrpCat GrpCat)
  map_mul' χ ψ := by
    apply NatTrans.ext
    funext U
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    rintro ⟨x⟩
    rfl

/-- The lifted character-section comparison commutes with restrictions. -/
def uliftInternalHomIso (F : Cᵒᵖ ⥤ GrpCat.{u}) (K : Cᵒᵖ ⥤ CommGrpCat.{u}) :
    CommutativeSheavesAb.Construction.CommutativeSheaves.internalHom F K ≅ CommutativeSheavesAb.Construction.CommutativeSheaves.internalHom (F ⋙ GrpCat.uliftFunctor.{u + 1, u})
      (K ⋙ CommGrpCat.uliftFunctor.{u + 1, u}) :=
  NatIso.ofComponents (fun T => (uliftInternalHomMulEquiv F K T).toCommGrpIso) (by
    intro T U f
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro χ
    apply NatTrans.ext
    rfl)

end SheafCharacterComparison.Construction.CommutativeSheaves

/-- Original native character sections and the characters of the
represented sheaf in the common universe are naturally equivalent groups. -/
def SheafCharacterComparison.Construction.Schemes.representedCharacterSectionsMulEquiv (S : Scheme.{u}) (G : Grp (Over S)) [IsCommMonObj G.X]
    (T : Over S) : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T) ≃*
      (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G)).obj.obj (Opposite.op T) :=
  SheafCharacterComparison.Construction.CommutativeSheaves.uliftInternalHomMulEquiv (yonedaGrp.obj G)
    (CharacterGroupSheaf.Construction.Schemes.commGroupPoints S (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S)) (Opposite.op T)

/-- Comparing the original and common-universe character sheaves
retains their full commutative-group structure. -/
def SheafCharacterComparison.Construction.Schemes.representedCharacterSheafIso (S : Scheme.{u}) (G : Grp (Over S)) [IsCommMonObj G.X] :
    CharacterGroupSheaf.Construction.Schemes.characterCommGroupSheaf S G ≅ CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (SheafCharacterComparison.Construction.CommutativeSheaves.uliftInternalHomIso (yonedaGrp.obj G)
      (CharacterGroupSheaf.Construction.Schemes.commGroupPoints S (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S)))

/-- A native character representative represents the original
character sheaf as a commutative-group sheaf in the common universe. -/
def GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.nativeRepresentedCharacterSheafIso
    {S : Scheme.{u}} {G : Grp (Over S)} (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) :
    @CommutativeSheavesAb.Construction.Schemes.representedFppfAb S D.dual D.commutative ≅ CharacterGroupSheaf.Construction.Schemes.characterCommGroupSheaf S G := by
  let e (T : (Over S)ᵒᵖ) :
      (@CommutativeSheavesAb.Construction.Schemes.representedFppfAb S D.dual D.commutative).obj.obj T ≃*
        (CharacterGroupSheaf.Construction.Schemes.characterCommGroupSheaf S G).obj.obj T :=
    MulEquiv.ulift.trans (D.sectionEquiv T.unop)
  apply (fullyFaithfulSheafToPresheaf _ _).preimageIso
  refine NatIso.ofComponents (fun T => (e T).toCommGrpIso) ?_
  intro T U f
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨d⟩
  exact D.sectionEquiv_natural f.unop d

/-- The actual Cartier dual of a represented sheaf is represented by
its native character group, with the canonical point-character comparison. -/
def GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.representedCartierDualIso
    {S : Scheme.{u}} {G : Grp (Over S)} [IsCommMonObj G.X]
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) :
    @CommutativeSheavesAb.Construction.Schemes.representedFppfAb S D.dual D.commutative ≅ CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) :=
  D.nativeRepresentedCharacterSheafIso ≪≫ SheafCharacterComparison.Construction.Schemes.representedCharacterSheafIso S G

/-- The canonical representation gives the point-character equivalence
on the common-universe sheaves. -/
def GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.representedCartierDualSectionsMulEquiv
    {S : Scheme.{u}} {G : Grp (Over S)} [IsCommMonObj G.X]
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (T : Over S) :
    (@CommutativeSheavesAb.Construction.Schemes.representedFppfAb S D.dual D.commutative).obj.obj (Opposite.op T) ≃*
      (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G)).obj.obj (Opposite.op T) :=
  (((sheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1}).mapIso
    D.representedCartierDualIso).app (Opposite.op T)).commGroupIsoToMulEquiv

/-- The sheaf isomorphism has the specified point-character formula. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.representedCartierDualIso_apply
    {S : Scheme.{u}} {G : Grp (Over S)} [IsCommMonObj G.X]
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (T : Over S)
    (d : (@CommutativeSheavesAb.Construction.Schemes.representedFppfAb S D.dual D.commutative).obj.obj (Opposite.op T)) :
    D.representedCartierDualIso.hom.hom.app (Opposite.op T) d =
      D.representedCartierDualSectionsMulEquiv T d := rfl

/-- The represented sheaf pairing is exactly the universe lift of
the native Cartier pairing. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.representedCartierDualIso_value
    {S : Scheme.{u}} {G : Grp (Over S)} [IsCommMonObj G.X]
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (T : Over S) (d : T ⟶ D.dual.X) (x : T ⟶ G.X) :
    SheafEvaluation.Construction.Schemes.sheafCharacterValue (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) T
      (D.representedCartierDualIso.hom.hom.app (Opposite.op T) (ULift.up d)) (ULift.up x) =
        ULift.up (D.evaluationValue T d x) := rfl

/-- Finite locally free representability of a commutative fppf sheaf
means representation by an actual finite locally free commutative group scheme. -/
def SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb (S : Scheme.{u}) (F : CommutativeSheavesAb.Construction.Schemes.FppfAb S) : Prop :=
  ∃ (G : Grp (Over S)) (hc : IsCommMonObj G.X), IsFinite G.X.hom ∧ Flat G.X.hom ∧
    LocallyOfFinitePresentation G.X.hom ∧ Nonempty (@CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G hc ≅ F)

/-- Finite locally free representability is invariant under sheaf isomorphism. -/
theorem SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb.of_iso {S : Scheme.{u}} {F K : CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (h : SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S F) (e : F ≅ K) : SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S K := by
  obtain ⟨G, hc, hf, hflat, hfp, ⟨a⟩⟩ := h
  exact ⟨G, hc, hf, hflat, hfp, ⟨a ≪≫ e⟩⟩

/-- Native finite locally free character representability yields the
corresponding representability conclusion for the actual sheaf Cartier dual. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.sheafDual_finiteLocallyFree
    {S : Scheme.{u}} {G : Grp (Over S)} [IsCommMonObj G.X]
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) :
    SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G)) :=
  ⟨D.dual, D.commutative, D.finite, D.flat, D.finitelyPresented, ⟨D.representedCartierDualIso⟩⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality
