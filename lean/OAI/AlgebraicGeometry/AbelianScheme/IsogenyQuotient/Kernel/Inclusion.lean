import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Subgroup
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupMaps

/-! # Inclusion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Inclusion.Construction

noncomputable section

/-!
The finite subgroup model embeds as a closed group subscheme of the
base-changed abelian scheme. Both group laws come from their actual functors
of points, and compatibility of the inclusion with them is proved.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]

local instance : CartesianMonoidalCategory (Over P) := Over.cartesianMonoidalCategory P
local instance : BraidedCategory (Over P) := Over.braidedCategory P

/-- All sections of the base-changed ambient group. -/
def fullRelativeSubgroup (A P : Over S) [GrpObj A] : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P where
  points _ _ := ⊤
  naturality := by
    intro X Y f t a ha
    trivial

def ambientPointGroups_representable :
    (Subgroup.Construction.relativePointGroups (fullRelativeSubgroup A P) ⋙ forget CommGrpCat).RepresentableBy
      (Over.mk (fst P A)) := by
  let toPoint {X : Over P} (h : X ⟶ Over.mk (fst P A)) :
      (fullRelativeSubgroup A P).points X.left X.hom := ⟨h.left ≫ snd P A, trivial⟩
  have hinj (X : Over P) : Function.Injective (@toPoint X) := by
    intro h k hhk
    apply Over.OverMorphism.ext
    apply hom_ext
    · exact h.w.trans k.w.symm
    · exact congrArg Subtype.val hhk
  have hsurj (X : Over P) : Function.Surjective (@toPoint X) := by
    intro a
    exact ⟨Over.homMk (lift X.hom a.val) (lift_fst _ _), Subtype.ext (lift_snd _ _)⟩
  refine {
    homEquiv := fun {X} => Equiv.ofBijective (@toPoint X) ⟨hinj X, hsurj X⟩
    homEquiv_comp := ?_
  }
  intro X X' f g
  apply Subtype.ext
  change (f.left ≫ g.left) ≫ snd P A = f.left ≫ (g.left ≫ snd P A)
  exact Category.assoc _ _ _

def relativeAmbientCommGroup : CommGrp (Over P) := by
  letI : CommGrpObj (Over.mk (fst P A)) :=
    CommGrpObj.ofRepresentableBy (Over.mk (fst P A))
      (Subgroup.Construction.relativePointGroups (fullRelativeSubgroup A P)) ambientPointGroups_representable
  exact CommGrp.mk (Over.mk (fst P A))

/-- Inclusion of the subgroup's point groups into the ambient point groups. -/
def relativePointInclusion (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) :
    Subgroup.Construction.relativePointGroups F ⟶ Subgroup.Construction.relativePointGroups (fullRelativeSubgroup A P) where
  app _ := CommGrpCat.ofHom {
    toFun a := ⟨a.val, trivial⟩
    map_one' := rfl
    map_mul' _ _ := rfl
  }
  naturality _ _ _ := rfl

def relativeModelInclusion
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model) :
    (Subgroup.Construction.relativeModelCommGroup F R).X ⟶ (relativeAmbientCommGroup (A := A) (P := P)).X :=
  Over.homMk (lift R.toBase R.toGroup) (lift_fst _ _)

/-- The geometric inclusion respects the group laws supplied by Yoneda. -/
theorem relativeModelInclusion_isMonHom
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model) :
    IsMonHom (relativeModelInclusion F R) := by
  apply GroupMaps.Construction.represented_group_map_isMonHom
    (Subgroup.Construction.relativePointGroups F ⋙ forget₂ CommGrpCat GrpCat)
    (Subgroup.Construction.relativePointGroups (fullRelativeSubgroup A P) ⋙ forget₂ CommGrpCat GrpCat)
    (Subgroup.Construction.relativePointGroups_representable F R) ambientPointGroups_representable
    (Functor.whiskerRight (relativePointInclusion F) (forget₂ CommGrpCat GrpCat))
  intro X x
  apply Subtype.ext
  change (x.left ≫ lift R.toBase R.toGroup) ≫ snd P A = x.left ≫ R.toGroup
  rw [Category.assoc, lift_snd]

def relativeSubgroupHom
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model) :
    Subgroup.Construction.relativeModelCommGroup F R ⟶ relativeAmbientCommGroup (A := A) (P := P) := by
  have : IsMonHom (relativeModelInclusion F R) := relativeModelInclusion_isMonHom F R
  exact ⟨Grp.homMk (relativeModelInclusion F R)⟩

/-- The ambient family over the underlying parameter scheme. -/
def ambientGroupScheme (A P : Over S) [GrpObj A] [IsCommMonObj A] :
    CommGrp (Over P.left) := by
  let e := Over.iteratedSliceEquiv P
  letI : e.functor.Braided := Functor.Braided.ofChosenFiniteProducts e.functor
  exact e.functor.mapCommGrp.obj (relativeAmbientCommGroup (A := A) (P := P))

/-- The actual inclusion of commutative group schemes over the parameter. -/
def subgroupInclusion
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model) :
    Subgroup.Construction.subgroupGroupScheme F R ⟶ ambientGroupScheme A P := by
  let e := Over.iteratedSliceEquiv P
  letI : e.functor.Braided := Functor.Braided.ofChosenFiniteProducts e.functor
  exact e.functor.mapCommGrp.map (relativeSubgroupHom F R)

theorem subgroupInclusion_underlying
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model) :
    (subgroupInclusion F R).hom.hom.hom.left = (lift R.toBase R.toGroup).left := rfl

/-- Thus FiniteDescent applies to the subgroup with its actual closed embedding,
rather than to an unrelated finite scheme with the same geometric points. -/
theorem subgroupInclusion_closedImmersion
    [IsSeparated A.hom] (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model) :
    IsClosedImmersion (subgroupInclusion F R).hom.hom.hom.left := by
  rw [subgroupInclusion_underlying]
  exact R.closedImmersion

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Inclusion.Construction
