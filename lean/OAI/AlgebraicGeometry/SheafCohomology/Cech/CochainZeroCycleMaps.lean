import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Cochain Zero Cycle Maps -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.CochainZeroCycleMaps.Projective

noncomputable section

/-! Direct functorial maps on degree-zero cycles, without passing through homology. -/

open _root_.CategoryTheory
universe u v

section Additive
variable {K L : CochainComplex AddCommGrpCat.{u} ℕ}

def addZeroCyclesMap (f : K ⟶ L) : (K.d 0 1).hom.ker →+ (L.d 0 1).hom.ker where
  toFun z := ⟨f.f 0 z, by
    have h := ConcreteCategory.congr_hom (f.comm 0 1) z.val
    change L.d 0 1 (f.f 0 z.val) = f.f 1 (K.d 0 1 z.val) at h
    exact h.trans ((congrArg (fun x => f.f 1 x) z.property).trans (map_zero _))⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)

theorem addZeroCyclesMap_bijective_of_split (f : K ⟶ L) (g : L ⟶ K)
    (hgf : g ≫ f = 𝟙 L) (hf : Function.Injective (f.f 0)) :
    Function.Bijective (addZeroCyclesMap f) := by
  constructor
  · intro x y h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  · intro z
    refine ⟨addZeroCyclesMap g z, Subtype.ext ?_⟩
    exact congrArg (fun h : L ⟶ L => h.f 0 z.val) hgf

def addZeroCyclesEquivOfIso (e : K ≅ L) : (K.d 0 1).hom.ker ≃+ (L.d 0 1).hom.ker :=
  AddEquiv.ofBijective (addZeroCyclesMap e.hom)
    (addZeroCyclesMap_bijective_of_split e.hom e.inv e.inv_hom_id
      (HomologicalComplex.eval AddCommGrpCat (.up ℕ) 0 |>.mapIso e).addCommGroupIsoToAddEquiv.injective)

end Additive

variable {R : Type u} [Ring R] {K L : CochainComplex (ModuleCat.{v} R) ℕ}

def linearZeroCyclesMap (f : K ⟶ L) : (K.d 0 1).hom.ker →ₗ[R] (L.d 0 1).hom.ker where
  toFun z := ⟨f.f 0 z, by
    have h := ConcreteCategory.congr_hom (f.comm 0 1) z.val
    change L.d 0 1 (f.f 0 z.val) = f.f 1 (K.d 0 1 z.val) at h
    exact h.trans ((congrArg (fun x => f.f 1 x) z.property).trans (map_zero _))⟩
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_smul' r x := Subtype.ext ((f.f 0).hom.map_smul r x.val)

theorem linearZeroCyclesMap_bijective_of_split (f : K ⟶ L) (g : L ⟶ K)
    (hgf : g ≫ f = 𝟙 L) (hf : Function.Injective (f.f 0)) :
    Function.Bijective (linearZeroCyclesMap f) := by
  constructor
  · intro x y h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  · intro z
    refine ⟨linearZeroCyclesMap g z, Subtype.ext ?_⟩
    exact congrArg (fun h : L ⟶ L => h.f 0 z.val) hgf

def linearZeroCyclesEquivOfIso (e : K ≅ L) : (K.d 0 1).hom.ker ≃ₗ[R] (L.d 0 1).hom.ker :=
  LinearEquiv.ofBijective (linearZeroCyclesMap e.hom)
    (linearZeroCyclesMap_bijective_of_split e.hom e.inv e.inv_hom_id
      (HomologicalComplex.eval (ModuleCat R) (.up ℕ) 0 |>.mapIso e).toLinearEquiv.injective)

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.CochainZeroCycleMaps.Projective
