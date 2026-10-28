import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.ExtCoefficientEdge

/-! # Augmentation Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.AugmentationNaturality

noncomputable section

/-! The actual frame coefficient augmentation commutes with maps of
augmented sheaf complexes. No acyclicity of the intermediate complex is
needed for this square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v z w

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {κ : Type v} (F : κ → C) (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C)
  [HasExt.{max u v z} (Sheaf J (ModuleCat.{max u v} R))]
  (K L : CochainComplex (Sheaf J (ModuleCat.{max u v} R)) ℕ)
  {Y : Sheaf J (ModuleCat.{max u v} R)}
  (a : (CochainComplex.single₀ _).obj Y ⟶ K)
  (b : (CochainComplex.single₀ _).obj Y ⟶ L)
  (g : K ⟶ L) (h : a ≫ g = b)

private instance moduleCoproducts (S : Type*) [CommRing S] : HasCoproducts.{0} (ModuleCat.{w} S) :=
  fun T => (ModuleCat.hasColimitsOfSize.{w, _, 0, 0} S).has_colimits_of_shape (Discrete T)

def bicomplexMap : ExtCoefficientEdge.bicomplex.{u, v, z} F R J K ⟶
    ExtCoefficientEdge.bicomplex.{u, v, z} F R J L :=
  ((ExtBicomplex.liftedFunctor.{u, v, z} F R J).mapHomologicalComplex (.up ℕ)).map g

def totalMap : (ExtCoefficientEdge.bicomplex.{u, v, z} F R J K).total (.up ℕ) ⟶
    (ExtCoefficientEdge.bicomplex.{u, v, z} F R J L).total (.up ℕ) :=
  HomologicalComplex₂.total.map (bicomplexMap.{u, v, z} F R J K L g) (.up ℕ)

include h in
theorem row_square :
    ExtCoefficientEdge.rowMap.{u, v, z} F R J K a ≫
      (bicomplexMap.{u, v, z} F R J K L g).f 0 =
        𝟙 _ ≫ ExtCoefficientEdge.rowMap.{u, v, z} F R J L b := by
  change (ExtBicomplex.liftedFunctor.{u, v, z} F R J).map (a.f 0) ≫
    (ExtBicomplex.liftedFunctor.{u, v, z} F R J).map (g.f 0) = _
  rw [← Functor.map_comp, Category.id_comp]
  exact congrArg (ExtBicomplex.liftedFunctor.{u, v, z} F R J).map
    (congrArg (fun t => t.f 0) h)

include h in
theorem square : ExtCoefficientEdge.edge.{u, v, z} F R J K a ≫
    totalMap.{u, v, z} F R J K L g =
      ExtCoefficientEdge.edge.{u, v, z} F R J L b := by
  exact (BicomplexCoefficientEdge.naturality _ _
    (ExtCoefficientEdge.rowMap.{u, v, z} F R J K a)
    (ExtCoefficientEdge.closed.{u, v, z} F R J K a) _
    (ExtCoefficientEdge.rowMap.{u, v, z} F R J L b)
    (ExtCoefficientEdge.closed.{u, v, z} F R J L b)
    (bicomplexMap.{u, v, z} F R J K L g) (𝟙 _)
    (row_square.{u, v, z} F R J K L a b g h)).trans (Category.id_comp _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.AugmentationNaturality
