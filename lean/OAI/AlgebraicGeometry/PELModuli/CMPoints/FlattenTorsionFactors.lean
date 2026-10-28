import Mathlib

/-! # Flatten Torsion Factors -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.FlattenTorsionFactors

noncomputable section

section

/-! Finite products of group-valued functors and their natural characters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {C : Type*} [Category* C] {I : Type} [Fintype I]

local instance forgottenCommGroup (K : C ⥤ CommGrpCat) (T : C) :
    CommGroup ((K ⋙ forget₂ CommGrpCat GrpCat).obj T) :=
  inferInstanceAs (CommGroup (K.obj T))

def piGroupFunctor (F : I → C ⥤ CommGrpCat) : C ⥤ GrpCat where
  obj T := GrpCat.of (∀ i, (F i).obj T)
  map f := GrpCat.ofHom (MonoidHom.piMap (fun i => ((F i).map f).hom))
  map_id T := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    funext i
    exact (F i).map_id_apply T (x i)
  map_comp f h := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    funext i
    exact (F i).map_comp_apply f h (x i)

def piGroupInclusion (F : I → C ⥤ CommGrpCat) (i : I) : F i ⋙ forget₂ CommGrpCat GrpCat ⟶ piGroupFunctor F where
  app T := GrpCat.ofHom (MonoidHom.mulSingle (fun j => (F j).obj T) i)
  naturality T U f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    funext j
    change (Pi.mulSingle i ((F i).map f x) : ∀ j, (F j).obj U) j =
      (F j).map f ((Pi.mulSingle i x : ∀ j, (F j).obj T) j)
    by_cases hj : j = i
    · subst j
      simp
    · simp [Pi.mulSingle_eq_of_ne hj]

def piGroupCharacterAssemble (F : I → C ⥤ CommGrpCat) (K : C ⥤ CommGrpCat)
    (χ : ∀ i, F i ⋙ forget₂ CommGrpCat GrpCat ⟶ K ⋙ forget₂ CommGrpCat GrpCat) :
    piGroupFunctor F ⟶ K ⋙ forget₂ CommGrpCat GrpCat where
  app T := GrpCat.ofHom {
    toFun x := ∏ i, (χ i).app T (x i)
    map_one' := by simp
    map_mul' x y := by simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib] }
  naturality T U f := by
    ext x
    change (∏ i, (χ i).app U ((F i).map f (x i))) = (K.map f) (∏ i, (χ i).app T (x i))
    rw [map_prod]
    exact Finset.prod_congr rfl (fun i _ => (χ i).naturality_apply f (x i))

def piGroupCharactersEquiv (F : I → C ⥤ CommGrpCat) (K : C ⥤ CommGrpCat) :
    (piGroupFunctor F ⟶ K ⋙ forget₂ CommGrpCat GrpCat) ≃
      (∀ i, F i ⋙ forget₂ CommGrpCat GrpCat ⟶ K ⋙ forget₂ CommGrpCat GrpCat) where
  toFun χ i := piGroupInclusion F i ≫ χ
  invFun := piGroupCharacterAssemble F K
  left_inv χ := by
    ext T x
    change (∏ i, χ.app T (Pi.mulSingle i (x i))) = χ.app T x
    let h : (∀ i, (F i).obj T) →* K.obj T := (χ.app T).hom
    exact (map_prod h (fun i => Pi.mulSingle i (x i)) Finset.univ).symm.trans
      (congrArg h (Finset.univ_prod_mulSingle (show ∀ i, (F i).obj T from x)))
  right_inv χ := by
    funext i
    ext T x
    change (∏ j, (χ j).app T ((Pi.mulSingle i x : ∀ j, (F j).obj T) j)) = (χ i).app T x
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.mulSingle_eq_of_ne hj]
    · simp

end

/-! Assemble factorwise torsion decompositions into one actual natural
product decomposition, with the pairs of indices retained. -/

open _root_.CategoryTheory

variable {C : Type*} [Category* C] {I J : Type} [Fintype I] [Fintype J]

def flattenPiGroupIso (F : I → C ⥤ CommGrpCat) (G : I → J → C ⥤ CommGrpCat)
    (e : ∀ i, F i ⋙ forget₂ CommGrpCat GrpCat ≅ piGroupFunctor (G i)) :
    piGroupFunctor F ≅ piGroupFunctor (fun p : I × J => G p.1 p.2) :=
  NatIso.ofComponents (fun T => MulEquiv.toGrpIso {
    toFun x p := (e p.1).hom.app T (x p.1) p.2
    invFun y i := (e i).inv.app T (fun j => y (i, j))
    left_inv x := by
      funext i
      exact ConcreteCategory.congr_hom ((e i).app T).hom_inv_id (x i)
    right_inv y := by
      funext p
      exact congrFun (ConcreteCategory.congr_hom ((e p.1).app T).inv_hom_id
        (fun j => y (p.1, j))) p.2
    map_mul' x y := by
      funext p
      exact congrFun (map_mul ((e p.1).hom.app T).hom (x p.1) (y p.1)) p.2 }) (by
    intro T U a
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    funext p
    exact congrFun ((e p.1).hom.naturality_apply a (x p.1)) p.2)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.FlattenTorsionFactors
