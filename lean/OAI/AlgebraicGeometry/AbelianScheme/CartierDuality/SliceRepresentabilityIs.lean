import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Slice Representability Is -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SliceRepresentabilityIs.Construction.SliceRepresentability

noncomputable section

/-!
# CartierDuality: a representative on a slice gives a represented open piece
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {Z : C} {F : Cᵒᵖ ⥤ Type v} {Y : Over Z}
  (r : ((Over.forget Z).op ⋙ F).RepresentableBy Y)

/-- A relative representative has a universal section on its underlying object. -/
def universalSection : F.obj (Opposite.op Y.left) := r.homEquiv (𝟙 Y)

/-- The map from the underlying representable presheaf to the original
presheaf, induced by the relative universal section. -/
def canonicalMap : yoneda.obj Y.left ⟶ F := yonedaEquiv.symm (universalSection r)

omit [CartesianMonoidalCategory C] in
/-- On a morphism respecting the slice structure, the universal map
is exactly the given relative representation. -/
theorem canonicalMap_apply {W : Over Z} (a : W ⟶ Y) :
    (canonicalMap r).app (Opposite.op W.left) a.left = r.homEquiv a :=
  (r.homEquiv_eq a).symm

variable (X : C) (β : yoneda.obj X ⟶ F)

/-- The product with the base of the slice, as an object of that slice. -/
def productOver : Over Z := Over.mk (snd X Z)

/-- Over the product with the slice base, the section specified by β
determines a map to the local representative. -/
def productLift : productOver X ⟶ Y :=
  r.homEquiv.symm (F.map (fst X Z).op (yonedaEquiv β))

/-- The product lift has the expected section under the local representation. -/
theorem productLift_section :
    r.homEquiv (productLift r X β) = F.map (fst X Z).op (yonedaEquiv β) :=
  r.homEquiv.apply_symm_apply _

/-- The product lift and first projection form the represented
comparison square with the original section β. -/
theorem productLift_square :
    yoneda.map (productLift r X β).left ≫ canonicalMap r = yoneda.map (fst X Z) ≫ β := by
  apply yonedaEquiv.injective
  have hleft := (yonedaEquiv_comp (yoneda.map (productLift r X β).left) (canonicalMap r)).trans
    ((congrArg (fun a => (canonicalMap r).app _ a)
      (yonedaEquiv_yoneda_map (productLift r X β).left)).trans
      ((canonicalMap_apply r (productLift r X β)).trans (productLift_section r X β)))
  exact hleft.trans (yonedaEquiv_naturality β (fst X Z))

/-- Every compatible pair of maps to a local representative and a test
object factors uniquely through the product with the slice base. -/
theorem productLift_universal (U : C) (a : U ⟶ Y.left) (b : U ⟶ X)
    (h : (canonicalMap r).app (Opposite.op U) a = β.app (Opposite.op U) b) :
    ∃! c : U ⟶ X ⊗ Z,
      c ≫ (productLift r X β).left = a ∧ c ≫ fst X Z = b := by
  let W : Over Z := Over.mk (a ≫ Y.hom)
  let a' : W ⟶ Y := Over.homMk a rfl
  let c : U ⟶ X ⊗ Z := lift b (a ≫ Y.hom)
  let c' : W ⟶ productOver X := Over.homMk c (lift_snd b (a ≫ Y.hom))
  have hb : F.map b.op (yonedaEquiv β) = β.app (Opposite.op U) b :=
    (yonedaEquiv_naturality β b).trans
      ((yonedaEquiv_comp (yoneda.map b) β).trans
        (congrArg (fun x => β.app (Opposite.op U) x) (yonedaEquiv_yoneda_map b)))
  have hsection : r.homEquiv (c' ≫ productLift r X β) = r.homEquiv a' := by
    rw [r.homEquiv_comp]
    change F.map c.op (r.homEquiv (productLift r X β)) = _
    rw [productLift_section]
    have hc : F.map c.op (F.map (fst X Z).op (yonedaEquiv β)) =
        F.map b.op (yonedaEquiv β) := by
      rw [← F.map_comp_apply, ← op_comp]
      exact congrArg (fun p => F.map p.op (yonedaEquiv β)) (lift_fst b (a ≫ Y.hom))
    exact hc.trans (hb.trans (h.symm.trans (canonicalMap_apply r a')))
  have ha : c ≫ (productLift r X β).left = a :=
    congrArg (fun k : W ⟶ Y => k.left) (r.homEquiv.injective hsection)
  refine ⟨c, ⟨ha, lift_fst b (a ≫ Y.hom)⟩, ?_⟩
  intro d hd
  apply CartesianMonoidalCategory.hom_ext
  · exact hd.2.trans (lift_fst b (a ≫ Y.hom)).symm
  · have hw : (productLift r X β).left ≫ Y.hom = snd X Z := (productLift r X β).w
    have he : d ≫ snd X Z = a ≫ Y.hom :=
      (congrArg (fun k => d ≫ k) hw.symm).trans
        ((Category.assoc d (productLift r X β).left Y.hom).symm.trans
          (congrArg (fun k => k ≫ Y.hom) hd.1))
    exact he.trans (lift_snd b (a ≫ Y.hom)).symm

/-- Pulling a local representative back along any section is represented
by the product of the test object and the slice base. -/
theorem productLift_isPullback :
    IsPullback (yoneda.map (productLift r X β).left) (yoneda.map (fst X Z))
      (canonicalMap r) β := by
  let w := productLift_square r X β
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ w)
  apply evaluationJointlyReflectsLimits
  intro U
  have hp : IsPullback ((yoneda.map (productLift r X β).left).app U)
      ((yoneda.map (fst X Z)).app U) ((canonicalMap r).app U) (β.app U) := by
    apply (Types.isPullback_iff _ _ _ _).mpr
    refine ⟨?_, ?_, ?_⟩
    · exact congrArg (fun k => k.app U) w
    · intro a b hab
      have ha := congrArg (fun k => k.app U a) w
      obtain ⟨c, _, hc⟩ := productLift_universal r X β U.unop
        (a ≫ (productLift r X β).left) (a ≫ fst X Z) ha
      exact (hc a ⟨rfl, rfl⟩).trans (hc b ⟨hab.1.symm, hab.2.symm⟩).symm
    · intro a b hab
      obtain ⟨c, hc, _⟩ := productLift_universal r X β U.unop a b hab
      exact ⟨c, hc⟩
  exact (isLimitMapConePullbackConeEquiv ((evaluation Cᵒᵖ (Type v)).obj U) w).symm hp.isLimit

/-- The map from a slice representative is relatively representable. -/
theorem canonicalMap_relativelyRepresentable :
    yoneda.relativelyRepresentable (canonicalMap r) := by
  intro X β
  exact ⟨X ⊗ Z, fst X Z, yoneda.map (productLift r X β).left, productLift_isPullback r X β⟩

/-- A property of the product projections is inherited by the map
from a slice representative as a relatively representable morphism. -/
theorem canonicalMap_relative (P : MorphismProperty C) [P.RespectsIso]
    (hP : ∀ X : C, P (fst X Z)) : P.presheaf (canonicalMap r) := by
  apply MorphismProperty.relative.of_exists
  intro X β
  exact ⟨X ⊗ Z, yoneda.map (productLift r X β).left, fst X Z,
    productLift_isPullback r X β, hP X⟩

/-- Representatives of restrictions over a cover of the terminal
object jointly cover the original presheaf. -/
theorem canonicalMaps_locallySurjective (J : GrothendieckTopology C)
    {ι : Type v} (U : ι → C) (localObjects : ∀ i, Over (U i))
    (r : ∀ i, ((Over.forget (U i)).op ⋙ F).RepresentableBy (localObjects i))
    (hcover : Sieve.ofArrows U (fun i => toUnit (U i)) ∈ J (𝟙_ C)) :
    Presheaf.IsLocallySurjective J (Sigma.desc (fun i => canonicalMap (r i))) where
  imageSieve_mem {X} s := by
    refine J.superset_covering ?_ (J.pullback_stable (toUnit X) hcover)
    rintro V γ ⟨W, a, _, ⟨i⟩, _⟩
    let V' : Over (U i) := Over.mk a
    let c : V' ⟶ localObjects i := (r i).homEquiv.symm (F.map γ.op s)
    refine ⟨(Sigma.ι (fun j => yoneda.obj (localObjects j).left) i).app (Opposite.op V) c.left, ?_⟩
    have hi := congrArg (fun k => k.app (Opposite.op V) c.left)
      (Sigma.ι_comp_desc (fun j => canonicalMap (r j)) i)
    exact hi.trans ((canonicalMap_apply (r i) c).trans ((r i).homEquiv.apply_symm_apply _))

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SliceRepresentabilityIs.Construction.SliceRepresentability
