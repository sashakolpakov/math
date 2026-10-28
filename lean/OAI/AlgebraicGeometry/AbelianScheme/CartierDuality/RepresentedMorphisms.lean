import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafCharacterComparison
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafQuotients
import Mathlib.Algebra.Category.Grp.EpiMono

/-! # Represented Morphisms -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentedMorphisms

noncomputable section

/-!
# CartierDuality: morphisms between native group schemes and their commutative fppf sheaves
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.Schemes

/-- The represented commutative fppf-sheaf construction is fully
faithful on native commutative group schemes. -/
def representedFppfAbHomEquiv {S : Scheme.{u}} (G H : Grp (Over S))
    [IsCommMonObj G.X] [IsCommMonObj H.X] :
    (G ⟶ H) ≃ (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G ⟶ CommutativeSheavesAb.Construction.Schemes.representedFppfAb S H) :=
  yonedaGrpFullyFaithful.homEquiv.trans
    (((CommGrpCat.fullyFaithfulForget₂ToGrp.whiskeringRight (Over S)ᵒᵖ).homEquiv
      (X := CharacterGroupSheaf.Construction.Schemes.commGroupPoints S G) (Y := CharacterGroupSheaf.Construction.Schemes.commGroupPoints S H)).symm.trans
      ((((show CommGrpCat.uliftFunctor.{u + 1, u}.FullyFaithful from
          CommGrpCat.uliftFunctorFullyFaithful).whiskeringRight (Over S)ᵒᵖ).homEquiv
        (X := CharacterGroupSheaf.Construction.Schemes.commGroupPoints S G) (Y := CharacterGroupSheaf.Construction.Schemes.commGroupPoints S H)).trans
        ((fullyFaithfulSheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1}).homEquiv
          (X := CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) (Y := CommutativeSheavesAb.Construction.Schemes.representedFppfAb S H)).symm))

/-- The represented commutative sheaf morphism of a native group morphism. -/
def representedFppfAbMap {S : Scheme.{u}} {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] (f : G ⟶ H) :
    CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G ⟶ CommutativeSheavesAb.Construction.Schemes.representedFppfAb S H :=
  representedFppfAbHomEquiv G H f

/-- The represented morphism acts by the original native morphism on points. -/
theorem representedFppfAbMap_apply {S : Scheme.{u}} {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] (f : G ⟶ H) (T : Over S) (x : T ⟶ G.X) :
    (representedFppfAbMap f).hom.app (Opposite.op T) (ULift.up x) =
      ULift.up (x ≫ f.hom.hom) := rfl

/-- The represented sheaf morphisms preserve native identities. -/
theorem representedFppfAbMap_id {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] :
    representedFppfAbMap (𝟙 G) = 𝟙 (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) := by
  apply (sheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1}).map_injective
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨x⟩
  exact congrArg ULift.up (Category.comp_id x)

/-- The represented sheaf morphisms preserve native composition. -/
theorem representedFppfAbMap_comp {S : Scheme.{u}} {G H K : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] [IsCommMonObj K.X] (f : G ⟶ H) (g : H ⟶ K) :
    representedFppfAbMap (f ≫ g) = representedFppfAbMap f ≫ representedFppfAbMap g := by
  apply (sheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1}).map_injective
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨x⟩
  exact congrArg ULift.up (Category.assoc x f.hom.hom g.hom.hom).symm

/-- Forgetting the commutative group law gives the original represented
map of type-valued fppf sheaves. -/
theorem representedFppfAbMap_forget {S : Scheme.{u}} {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] (f : G ⟶ H) :
    (sheafCompose (Scheme.fppfTopology.over S) (forget CommGrpCat.{u + 1})).map
      (representedFppfAbMap f) =
        (Scheme.fppfTopology.over S).uliftYoneda.map f.hom.hom := rfl

/-- A monomorphism of represented commutative fppf sheaves is a
monomorphism of the underlying native schemes over the base. -/
theorem representedFppfAbMap_mono_underlying {S : Scheme.{u}} {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] (f : G ⟶ H) [Mono (representedFppfAbMap f)] :
    Mono f.hom.hom := by
  constructor
  intro T x y hxy
  have hm : Mono ((representedFppfAbMap f).hom.app (Opposite.op T)) := inferInstance
  have he : ULift.up.{u + 1} x = ULift.up.{u + 1} y :=
    (CommGrpCat.mono_iff_injective ((representedFppfAbMap f).hom.app (Opposite.op T))).mp hm
      ((representedFppfAbMap_apply f T x).trans
        ((congrArg ULift.up hxy).trans (representedFppfAbMap_apply f T y).symm))
  exact congrArg ULift.down he

/-- A native group monomorphism gives a monomorphism of the actual
represented commutative fppf sheaves. -/
theorem representedFppfAbMap_mono {S : Scheme.{u}} {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] (f : G ⟶ H) [Mono f.hom.hom] :
    Mono (representedFppfAbMap f) := by
  constructor
  intro Z a b hab
  apply (sheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1}).map_injective
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  apply ULift.ext
  apply (cancel_mono f.hom.hom).mp
  exact congrArg ULift.down (congrArg
    (fun c : Z ⟶ CommutativeSheavesAb.Construction.Schemes.representedFppfAb S H => c.hom.app T x) hab)

/-- A finite represented subgroup of a separated group scheme is a
closed subgroup scheme, including in the nonreduced case. -/
theorem representedFppfAbMap_closedImmersion {S : Scheme.{u}} {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] [IsFinite G.X.hom] [IsSeparated H.X.hom]
    (f : G ⟶ H) [Mono (representedFppfAbMap f)] : IsClosedImmersion f.hom.hom.left := by
  let : Mono f.hom.hom := representedFppfAbMap_mono_underlying f
  let : IsFinite (f.hom.hom.left ≫ H.X.hom) := f.hom.hom.w.symm ▸ inferInstanceAs (IsFinite G.X.hom)
  let : IsFinite f.hom.hom.left := IsFinite.of_comp f.hom.hom.left H.X.hom
  exact (IsClosedImmersion.iff_isFinite_and_mono f.hom.hom.left).mpr ⟨inferInstance, inferInstance⟩

end Construction.Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentedMorphisms
