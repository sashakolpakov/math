import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafTranspose
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Block
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafQuotients

/-! # Sheaf Blocks -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality

noncomputable section

/-!
# CartierDuality: actual restricted pairings on adjoint direct factors
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

namespace SheafBlocks.Construction.SelfDuality

variable {C : Type u} [Category.{v} C] (D : Cᵒᵖ ⥤ C)
    (β : ∀ X : C, X ⟶ D.obj (Opposite.op (D.obj (Opposite.op X))))

/-- Transposition turns precomposition into character restriction. -/
theorem transpose_precomp {X X' Y : C} (i : X' ⟶ X) (a : X ⟶ D.obj (Opposite.op Y)) :
    SheafTranspose.Construction.SelfDuality.transpose D β (i ≫ a) = SheafTranspose.Construction.SelfDuality.transpose D β a ≫ D.map i.op := by
  simp only [SheafTranspose.Construction.SelfDuality.transpose, op_comp, D.map_comp, Category.assoc]

/-- Transposition turns character restriction into precomposition. -/
theorem transpose_postcomp
    (hn : ∀ {X Y : C} (f : X ⟶ Y), β X ≫ D.map (D.map f.op).op = f ≫ β Y)
    {X Y Y' : C} (a : X ⟶ D.obj (Opposite.op Y)) (j : Y' ⟶ Y) :
    SheafTranspose.Construction.SelfDuality.transpose D β (a ≫ D.map j.op) = j ≫ SheafTranspose.Construction.SelfDuality.transpose D β a := by
  rw [SheafTranspose.Construction.SelfDuality.transpose, op_comp, D.map_comp, ← Category.assoc, hn j, Category.assoc]
  rfl

/-- The transpose of a restricted pairing is the restriction of its transpose. -/
theorem transpose_restrict
    (hn : ∀ {X Y : C} (f : X ⟶ Y), β X ≫ D.map (D.map f.op).op = f ≫ β Y)
    {X Y X' Y' : C} (a : X ⟶ D.obj (Opposite.op Y)) (i : X' ⟶ X) (j : Y' ⟶ Y) :
    SheafTranspose.Construction.SelfDuality.transpose D β (i ≫ a ≫ D.map j.op) = j ≫ SheafTranspose.Construction.SelfDuality.transpose D β a ≫ D.map i.op := by
  rw [transpose_precomp, transpose_postcomp D β hn, Category.assoc]

/-- Adjointness is preserved when transposing a pairing. -/
theorem transpose_adjoint
    (hn : ∀ {X Y : C} (f : X ⟶ Y), β X ≫ D.map (D.map f.op).op = f ≫ β Y)
    {X Y : C} (a : X ⟶ D.obj (Opposite.op Y)) (p : X ⟶ X) (q : Y ⟶ Y)
    (h : p ≫ a = a ≫ D.map q.op) :
    q ≫ SheafTranspose.Construction.SelfDuality.transpose D β a = SheafTranspose.Construction.SelfDuality.transpose D β a ≫ D.map p.op := by
  have ht := congrArg (SheafTranspose.Construction.SelfDuality.transpose D β) h
  rw [transpose_precomp, transpose_postcomp D β hn] at ht
  exact ht.symm

end SheafBlocks.Construction.SelfDuality

/-- Restriction of the actual bilinear pairing along two sheaf maps. -/
def SheafEvaluation.Construction.Schemes.BilinearPairing.restrict {S : Scheme.{u}} {G K G' K' : CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (e : SheafEvaluation.Construction.Schemes.BilinearPairing G K) (i : G' ⟶ G) (j : K' ⟶ K) : SheafEvaluation.Construction.Schemes.BilinearPairing G' K' :=
  ⟨i ≫ e.leftAdjoint ≫ (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map j.op⟩

/-- Both adjoints of restriction are the actual restricted adjoints. -/
theorem SheafEvaluation.Construction.Schemes.BilinearPairing.restrict_rightAdjoint {S : Scheme.{u}} {G K G' K' : CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (e : SheafEvaluation.Construction.Schemes.BilinearPairing G K) (i : G' ⟶ G) (j : K' ⟶ K) :
    (e.restrict i j).rightAdjoint = j ≫ e.rightAdjoint ≫ (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map i.op :=
  SheafBlocks.Construction.SelfDuality.transpose_restrict (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S) SheafEvaluation.Construction.Schemes.sheafBidualEvaluation
    (fun a => SheafEvaluation.Construction.Schemes.sheafBidualEvaluation_natural a) e.leftAdjoint i j

/-- Projectors are adjoint when their actions give the same pairing
value on every test scheme. Perfection is not part of this condition. -/
def SheafBlocks.Construction.Schemes.ProjectorsAdjoint {S : Scheme.{u}} {G K : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (e : SheafEvaluation.Construction.Schemes.BilinearPairing G K)
    (p : G ⟶ G) (q : K ⟶ K) : Prop :=
  ∀ (T : Over S) (x : G.obj.obj (Opposite.op T)) (y : K.obj.obj (Opposite.op T)),
    SheafEvaluation.Construction.Schemes.sheafCharacterValue G T (e.rightAdjoint.hom.app (Opposite.op T) y)
        (p.hom.app (Opposite.op T) x) =
      SheafEvaluation.Construction.Schemes.sheafCharacterValue G T (e.rightAdjoint.hom.app (Opposite.op T)
        (q.hom.app (Opposite.op T) y)) x

/-- Pointwise adjointness is the corresponding equality of character-valued maps. -/
theorem SheafBlocks.Construction.Schemes.ProjectorsAdjoint.right_map {S : Scheme.{u}} {G K : CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    {e : SheafEvaluation.Construction.Schemes.BilinearPairing G K} {p : G ⟶ G} {q : K ⟶ K} (h : SheafBlocks.Construction.Schemes.ProjectorsAdjoint e p q) :
    q ≫ e.rightAdjoint = e.rightAdjoint ≫ (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map p.op := by
  apply SheafEvaluation.Construction.Schemes.sheafDualHom_ext
  intro T y x
  exact (h T x y).symm.trans
    (SheafEvaluation.Construction.Schemes.cartierDualSheafMap_value p T (e.rightAdjoint.hom.app (Opposite.op T) y) x).symm

/-- The same pointwise adjointness gives the equality for the other adjoint. -/
theorem SheafBlocks.Construction.Schemes.ProjectorsAdjoint.left_map {S : Scheme.{u}} {G K : CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    {e : SheafEvaluation.Construction.Schemes.BilinearPairing G K} {p : G ⟶ G} {q : K ⟶ K} (h : SheafBlocks.Construction.Schemes.ProjectorsAdjoint e p q) :
    p ≫ e.leftAdjoint = e.leftAdjoint ≫ (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map q.op := by
  have ht := SheafBlocks.Construction.SelfDuality.transpose_adjoint (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S) SheafEvaluation.Construction.Schemes.sheafBidualEvaluation
    (fun a => SheafEvaluation.Construction.Schemes.sheafBidualEvaluation_natural a) e.rightAdjoint q p h.right_map
  have he : SheafTranspose.Construction.SelfDuality.transpose (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S) SheafEvaluation.Construction.Schemes.sheafBidualEvaluation e.rightAdjoint =
      e.leftAdjoint := congrArg SheafEvaluation.Construction.Schemes.BilinearPairing.leftAdjoint e.flip_flip
  rw [he] at ht
  exact ht

/-- A perfect sheaf pairing restricts to a perfect pairing on two
direct factors whose actual projection idempotents are adjoint. -/
theorem SheafEvaluation.Construction.Schemes.BilinearPairing.restrict_isPerfect {S : Scheme.{u}} {G K G' K' : CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (e : SheafEvaluation.Construction.Schemes.BilinearPairing G K) (he : e.IsPerfect)
    (i : G' ⟶ G) (r : G ⟶ G') (hi : i ≫ r = 𝟙 G')
    (j : K' ⟶ K) (s : K ⟶ K') (hj : j ≫ s = 𝟙 K')
    (hadj : SheafBlocks.Construction.Schemes.ProjectorsAdjoint e (r ≫ i) (s ≫ j)) : (e.restrict i j).IsPerfect := by
  let el : G ≅ CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf K := @asIso _ _ _ _ e.leftAdjoint he.1
  let er : K ≅ CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G := @asIso _ _ _ _ e.rightAdjoint he.2
  have hleft : IsIso (e.restrict i j).leftAdjoint :=
    (Block.Construction.Blocks.adjointFactorsIso (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S) el
      j s hj i r hi hadj.left_map).isIso_hom
  have hright : IsIso (j ≫ e.rightAdjoint ≫ (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map i.op) :=
    (Block.Construction.Blocks.adjointFactorsIso (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S) er
      i r hi j s hj hadj.right_map).isIso_hom
  exact ⟨hleft, (e.restrict_rightAdjoint i j).symm ▸ hright⟩

structure SheafBlocks.Construction.Schemes.SheafBlockDecomposition {S : Scheme.{u}} (G : CommutativeSheavesAb.Construction.Schemes.FppfAb S) (I : Type u) where
  block : I → CommutativeSheavesAb.Construction.Schemes.FppfAb S
  productIso : G ≅ ∏ᶜ block

namespace SheafBlocks.Construction.Schemes.SheafBlockDecomposition

variable {S : Scheme.{u}} {G : CommutativeSheavesAb.Construction.Schemes.FppfAb S} {I : Type u} (B : SheafBlockDecomposition G I)

/-- The block projection furnished by the product decomposition. -/
def projection (i : I) : G ⟶ B.block i := B.productIso.hom ≫ Pi.π B.block i

/-- Insert into one block with the identity in every other group block. -/
def inclusion (i : I) : B.block i ⟶ G := by
  classical
  exact Pi.lift (fun j => if h : i = j then eqToHom (congrArg B.block h) else 0) ≫ B.productIso.inv

/-- The actual block inclusion is a section of its projection. -/
theorem inclusion_projection (i : I) : B.inclusion i ≫ B.projection i = 𝟙 (B.block i) := by
  classical
  simp [SheafBlockDecomposition.inclusion, SheafBlockDecomposition.projection]

/-- The canonical projection idempotent on the ambient group sheaf. -/
def projector (i : I) : G ⟶ G := B.projection i ≫ B.inclusion i

/-- The canonical block projector is idempotent. -/
theorem projector_idempotent (i : I) : B.projector i ≫ B.projector i = B.projector i := by
  dsimp [SheafBlockDecomposition.projector]
  rw [Category.assoc, ← Category.assoc (B.inclusion i), B.inclusion_projection, Category.id_comp]

/-- Restrict the original pairing to two actual blocks. -/
def restrictedPairing (e : SheafEvaluation.Construction.Schemes.BilinearPairing G G) (i j : I) : SheafEvaluation.Construction.Schemes.BilinearPairing (B.block i) (B.block j) :=
  e.restrict (B.inclusion i) (B.inclusion j)

/-- Adjoint projectors give a perfect pairing on their two blocks. -/
theorem restrictedPairing_isPerfect (e : SheafEvaluation.Construction.Schemes.BilinearPairing G G) (he : e.IsPerfect) (i j : I)
    (h : ProjectorsAdjoint e (B.projector i) (B.projector j)) :
    (B.restrictedPairing e i j).IsPerfect :=
  e.restrict_isPerfect he (B.inclusion i) (B.projection i) (B.inclusion_projection i)
    (B.inclusion j) (B.projection j) (B.inclusion_projection j) h

end SheafBlocks.Construction.Schemes.SheafBlockDecomposition

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality
