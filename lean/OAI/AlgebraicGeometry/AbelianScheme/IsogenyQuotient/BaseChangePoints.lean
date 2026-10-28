import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Polarization

/-! # Base Change Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BaseChangePoints.Construction

noncomputable section

/-!
Compatibility between field-level polarizations and the point-group input
used by the relative construction. The equivalence between points and
sections of the base change is built from the actual fiber product and
proved multiplicative; naturality is not assumed as an extra interface law.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S T : Scheme.{u}} (s : T ⟶ S)

def diagonalSection :
    (𝟙_ (Over T)) ⟶ (Over.pullback s).obj (Over.mk s) :=
  Over.homMk (pullback.diagonal s) (pullback.diagonal_snd s)

def pointSectionMap (X : Over S) [GrpObj X] :
    (Over.mk s ⟶ X) →* ((𝟙_ (Over T)) ⟶ (Over.pullback s).obj X) :=
  ((yonedaGrpObj ((Over.pullback s).obj X)).map (diagonalSection s).op).hom.comp
    (Over.pullback s).homMonoidHom

theorem pointSectionMap_apply (X : Over S) [GrpObj X] (a : Over.mk s ⟶ X) :
    pointSectionMap s X a = diagonalSection s ≫ (Over.pullback s).map a := rfl

@[simp]
theorem pointSectionMap_fst
    (X : Over S) [GrpObj X] (a : Over.mk s ⟶ X) :
    (pointSectionMap s X a).left ≫ pullback.fst X.hom s = a.left := by
  simp only [pointSectionMap_apply,
    Over.comp_left, diagonalSection, Over.homMk_left, Over.pullback_map_left,
    Category.assoc, pullback.lift_fst]
  change pullback.diagonal s ≫ pullback.fst s s ≫ a.left = a.left
  rw [pullback.diagonal_fst_assoc]

theorem pointSectionMap_bijective (X : Over S) [GrpObj X] :
    Function.Bijective (pointSectionMap s X) := by
  constructor
  · intro a b hab
    apply Over.OverMorphism.ext
    have h := congrArg (fun x => x.left ≫ pullback.fst X.hom s) hab
    simpa only [pointSectionMap_fst] using h
  · intro x
    have hbase : (x.left ≫ pullback.fst X.hom s) ≫ X.hom = s := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      have hx : x.left ≫ pullback.snd X.hom s = 𝟙 T := x.w
      rw [hx]
      exact Category.id_comp s
    let a : Over.mk s ⟶ X := Over.homMk (x.left ≫ pullback.fst X.hom s) hbase
    refine ⟨a, ?_⟩
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pointSectionMap_fst s X a
    · exact (pointSectionMap s X a).w.trans x.w.symm

/-- Group-valued points equal sections of the actual base-changed group. -/
def pointSectionEquiv (X : Over S) [GrpObj X] :
    (Over.mk s ⟶ X) ≃* ((𝟙_ (Over T)) ⟶ (Over.pullback s).obj X) :=
  MulEquiv.ofBijective (pointSectionMap s X) (pointSectionMap_bijective s X)

theorem pointSectionMap_natural
    {X Y : Over S} [GrpObj X] [GrpObj Y]
    (f : X ⟶ Y) (a : Over.mk s ⟶ X) :
    pointSectionMap s Y (a ≫ f) =
      pointSectionMap s X a ≫ (Over.pullback s).map f := by
  change diagonalSection s ≫ (Over.pullback s).map (a ≫ f) =
    (diagonalSection s ≫ (Over.pullback s).map a) ≫ (Over.pullback s).map f
  rw [Functor.map_comp, Category.assoc]

/-- The point-group homomorphism induced by an actual morphism of the
base-changed groups. -/
def fieldMorphismOnPoints
    {X Y : Over S} [GrpObj X] [GrpObj Y]
    (p : (Over.pullback s).obj X ⟶ (Over.pullback s).obj Y) [IsMonHom p] :
    (Over.mk s ⟶ X) →* (Over.mk s ⟶ Y) :=
  (pointSectionEquiv s Y).symm.toMonoidHom.comp
    ((IsMonHom.monoidHom p (𝟙_ (Over T))).comp (pointSectionEquiv s X).toMonoidHom)

@[simp]
theorem fieldMorphismOnPoints_section
    {X Y : Over S} [GrpObj X] [GrpObj Y]
    (p : (Over.pullback s).obj X ⟶ (Over.pullback s).obj Y) [IsMonHom p]
    (a : Over.mk s ⟶ X) :
    pointSectionMap s Y (fieldMorphismOnPoints s p a) = pointSectionMap s X a ≫ p := by
  exact (pointSectionEquiv s Y).apply_symm_apply _

/-- The field-level polarization pullback identity implies precisely the
point-group identity consumed by relative_polarization_homomorphism. -/
theorem field_polarization_identity_on_points
    {A B AD BD : Over S} [GrpObj A] [GrpObj B] [GrpObj AD] [GrpObj BD]
    (n : ℕ) (f : A ⟶ B) (fd : BD ⟶ AD) (polarization : A ⟶ AD)
    (p : (Over.pullback s).obj B ⟶ (Over.pullback s).obj BD) [IsMonHom p]
    (h_PoincareBundle : (Over.pullback s).map f ≫ p ≫ (Over.pullback s).map fd =
      ((Over.pullback s).map polarization) ^ n)
    (a : Over.mk s ⟶ A) :
    fieldMorphismOnPoints s p (a ≫ f) ≫ fd = (a ≫ polarization) ^ n := by
  apply (pointSectionMap_bijective s AD).1
  rw [pointSectionMap_natural, fieldMorphismOnPoints_section, pointSectionMap_natural]
  rw [Category.assoc, Category.assoc, h_PoincareBundle, MonObj.comp_pow]
  rw [← pointSectionMap_natural]
  exact (pointSectionMap s AD).map_pow _ n |>.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BaseChangePoints.Construction
