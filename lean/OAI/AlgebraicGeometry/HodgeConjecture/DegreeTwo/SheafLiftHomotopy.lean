import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupHomotopy
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SheafComplexLift

/-! # Sheaf Lift Homotopy -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SheafLiftHomotopy.Constructions

noncomputable section

/-! Sheafification preserves the actual primitive identities used in the good shift. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R] {X : TopCat.{0}}

def sheafDegreeLift {P : X.Presheaf (ModuleCat.{0} R)}
    {F : TopCat.Sheaf (ModuleCat.{0} R) X} (f : P ⟶ F.obj) :
    (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)).obj P ⟶ F :=
  ⟨CategoryTheory.sheafifyLift (Opens.grothendieckTopology X) f F.property⟩

theorem sheafDegreeLift_unit {P : X.Presheaf (ModuleCat.{0} R)}
    {F : TopCat.Sheaf (ModuleCat.{0} R) X} (f : P ⟶ F.obj) :
    CategoryTheory.toSheafify (Opens.grothendieckTopology X) P ≫
      (sheafDegreeLift f).hom = f :=
  CategoryTheory.toSheafify_sheafifyLift _ _ _

theorem sheafDegreeLift_sub {P : X.Presheaf (ModuleCat.{0} R)}
    {F : TopCat.Sheaf (ModuleCat.{0} R) X} (f g : P ⟶ F.obj) :
    sheafDegreeLift (f-g) = sheafDegreeLift f - sheafDegreeLift g := by
  apply Sheaf.hom_ext
  apply CategoryTheory.sheafify_hom_ext _ _ _ F.property
  change CategoryTheory.toSheafify _ P ≫ (sheafDegreeLift (f-g)).hom =
    CategoryTheory.toSheafify _ P ≫ ((sheafDegreeLift f).hom - (sheafDegreeLift g).hom)
  rw [sheafDegreeLift_unit, comp_sub, sheafDegreeLift_unit, sheafDegreeLift_unit]

theorem sheafDegreeLift_add {P : X.Presheaf (ModuleCat.{0} R)}
    {F : TopCat.Sheaf (ModuleCat.{0} R) X} (f g : P ⟶ F.obj) :
    sheafDegreeLift (f+g) = sheafDegreeLift f + sheafDegreeLift g := by
  apply Sheaf.hom_ext
  apply CategoryTheory.sheafify_hom_ext _ _ _ F.property
  change CategoryTheory.toSheafify _ P ≫ (sheafDegreeLift (f+g)).hom =
    CategoryTheory.toSheafify _ P ≫ ((sheafDegreeLift f).hom + (sheafDegreeLift g).hom)
  rw [sheafDegreeLift_unit, comp_add, sheafDegreeLift_unit, sheafDegreeLift_unit]

theorem sheafDegreeLift_precomp {P Q : X.Presheaf (ModuleCat.{0} R)}
    {F : TopCat.Sheaf (ModuleCat.{0} R) X} (f : P ⟶ Q) (g : Q ⟶ F.obj) :
    sheafDegreeLift (f ≫ g) =
      (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)).map f ≫
        sheafDegreeLift g := by
  apply Sheaf.hom_ext
  exact (CategoryTheory.sheafifyMap_sheafifyLift _ f g F.property).symm

theorem sheafDegreeLift_postcomp {P : X.Presheaf (ModuleCat.{0} R)}
    {F G : TopCat.Sheaf (ModuleCat.{0} R) X} (f : P ⟶ F.obj) (g : F ⟶ G) :
    sheafDegreeLift (f ≫ g.hom) = sheafDegreeLift f ≫ g := by
  apply Sheaf.hom_ext
  exact CategoryTheory.sheafifyLift_comp _ f F.property g.hom G.property

variable {K : CochainComplex (X.Presheaf (ModuleCat.{0} R)) ℕ}
variable {L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ}

def sheafLiftTwoGoodShiftHomotopy
    (f g : K ⟶ AlgebraicTopology.Cohomology.Singular.SheafSections.sheafUnderlyingCochainComplex (L.restriction (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2)))
    (h : ∀ n, K.X (n+1) ⟶ (L.X (2+n)).obj) (v : K.X 0 ⟶ (L.X 1).obj)
    (hzero : f.f 0 - g.f 0 = K.d 0 1 ≫ h 0 + v ≫ (L.d 1 2).hom)
    (hsucc : ∀ n, f.f (n+1) - g.f (n+1) =
      K.d (n+1) (n+2) ≫ h (n+1) + h n ≫ (L.d (2+n) (2+(n+1))).hom) :
    Homotopy (SheafComplexLift.Constructions.sheafComplexLift f ≫ L.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2))
      (SheafComplexLift.Constructions.sheafComplexLift g ≫ L.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2)) := by
  apply RelativeCupHomotopy.Constructions.cochainTwoGoodShiftHomotopy (SheafComplexLift.Constructions.sheafComplexLift f) (SheafComplexLift.Constructions.sheafComplexLift g)
    (fun n => sheafDegreeLift (h n)) (sheafDegreeLift v)
  · have hz := congrArg sheafDegreeLift hzero
    rw [sheafDegreeLift_sub, sheafDegreeLift_add,
      sheafDegreeLift_precomp, sheafDegreeLift_postcomp] at hz
    exact hz
  · intro n
    have hs := congrArg sheafDegreeLift (hsucc n)
    rw [sheafDegreeLift_sub, sheafDegreeLift_add,
      sheafDegreeLift_precomp, sheafDegreeLift_postcomp] at hs
    exact hs

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SheafLiftHomotopy.Constructions
