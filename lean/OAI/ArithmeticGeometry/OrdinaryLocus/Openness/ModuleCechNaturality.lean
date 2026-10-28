import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechCocycles

/-! # Module Cech Naturality -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleCechNaturality.Construction

noncomputable section

/-! Naturality of the degree-zero Cech differential in its module-sheaf coefficients. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u v w

variable {R : Type u} [CommRing R] {X : TopCat.{v}}
    (F G : TopCat.Sheaf (ModuleCat.{v} R) X) (φ : F ⟶ G)
    {ι : Type w} (U : ι → Opens X)

theorem moduleSheaf_restriction_square {A B C D : Opens X}
    (i : B ⟶ A) (j : D ⟶ B) (i' : C ⟶ A) (j' : D ⟶ C) (x : F.obj.obj (op A)) :
    F.obj.map j.op (F.obj.map i.op x) = F.obj.map j'.op (F.obj.map i'.op x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← F.obj.map_comp, ← F.obj.map_comp]
  exact congrArg (fun q ↦ F.obj.map q x) (Subsingleton.elim _ _)

theorem openModuleCechD0_naturality (x : OpenCechDegreeZero.Construction.openModuleCechC0 F U) (i j : ι) :
    φ.hom.app (op (U i ⊓ U j)) (OpenCechDegreeZero.Construction.openModuleCechD0 F U x i j) =
      OpenCechDegreeZero.Construction.openModuleCechD0 G U (fun i ↦ φ.hom.app (op (U i)) (x i)) i j := by
  change φ.hom.app _ (F.obj.map (homOfLE inf_le_right).op (x j) -
    F.obj.map (homOfLE inf_le_left).op (x i)) = _
  exact (map_sub (φ.hom.app _).hom _ _).trans
    (congrArg₂ (fun a b ↦ a - b)
      (NatTrans.naturality_apply φ.hom (homOfLE inf_le_right).op (x j))
      (NatTrans.naturality_apply φ.hom (homOfLE inf_le_left).op (x i)))

theorem openModuleCech_boundary_of_factorization
    (H : TopCat.Sheaf (ModuleCat.{v} R) X) (ψ : F ⟶ H) (π : G ⟶ H) (hφ : φ ≫ π = ψ)
    (z : OpenCechDegreeZero.Construction.openModuleCechC1 F U) (y : OpenCechDegreeZero.Construction.openModuleCechC0 G U)
    (hy : ∀ i j, φ.hom.app (op (U i ⊓ U j)) (z i j) = OpenCechDegreeZero.Construction.openModuleCechD0 G U y i j) :
    ∀ i j, ψ.hom.app (op (U i ⊓ U j)) (z i j) =
      OpenCechDegreeZero.Construction.openModuleCechD0 H U (fun i ↦ π.hom.app (op (U i)) (y i)) i j := by
  intro i j
  have he := congrArg (fun q ↦ q.hom.app (op (U i ⊓ U j)) (z i j)) hφ
  exact he.symm.trans ((congrArg (π.hom.app (op (U i ⊓ U j))) (hy i j)).trans
    (openModuleCechD0_naturality G H π U y i j))

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleCechNaturality.Construction
