import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.MappedSingleCoordinates

/-! # Mapped Single Degree Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.MappedSingleDegreeCoordinates

noncomputable section

/-! Changing the degree of the original mapped single coefficient
preserves the actual unshifted principal-to-global comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.MappedSingleCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
variable {X : TopCat.{u}} {D : Type v} [Category D] [Abelian D]
  [HasProducts.{u} D] [HasCoproducts.{0} D]
  {A : Type w} [Category.{z} A] [Abelian A]
  (J : A ⥤ (Opens X)ᵒᵖ ⥤ D) [J.Additive] (M : A) (c d g : ℕ)
  {C : Type u} [Preorder C] [HasFiniteProducts C] (F : C ⥤ Opens X)
  {ι κ ν μ ρ : Type u}
  [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] [LinearOrder μ] [LinearOrder ρ]
  (W : ι → C)
  [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) F]
  (B : κ → Opens X) (E : ν → Opens X)
  (r : FormalCoproduct.mk ν E ⟶ FormalCoproduct.mk ι (F.obj ∘ W))
  (s : FormalCoproduct.mk ν E ⟶ FormalCoproduct.mk κ B)
  (V : μ → Opens X) (T : ρ → Opens X)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) B))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B E s (MappedSingleCoordinates.source J M c) (g+c))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (MappedSingleCoordinates.source J M c)) (g+c))]
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B E s (MappedSingleCoordinates.source J M d) (g+d))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (MappedSingleCoordinates.source J M d)) (g+d))]

def sourceIso := MappedSingleCoordinates.localCoordinates J M c g F W ≪≫ (MappedSingleCoordinates.localCoordinates J M d g F W).symm

def targetIso := MappedSingleCoordinates.globalCoordinates J M c g V ≪≫ (MappedSingleCoordinates.globalCoordinates J M d g V).symm

theorem coefficient_eq : MappedSingleCoordinates.coefficientComparison J M c g F W B E r s V T l t =
    MappedSingleCoordinates.coefficientComparison J M d g F W B E r s V T l t := rfl

theorem comparison :
    (sourceIso J M c d g F W).hom ≫
      PresheafCover.Comparison.comparison F W B E r s V T l t (MappedSingleCoordinates.source J M d) (g+d) =
    PresheafCover.Comparison.comparison F W B E r s V T l t (MappedSingleCoordinates.source J M c) (g+c) ≫
      (targetIso J M c d g V).hom := by
  apply (cancel_mono (MappedSingleCoordinates.globalCoordinates J M d g V).hom).mp
  simp only [sourceIso, targetIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [MappedSingleCoordinates.comparison J M d g F W B E r s V T l t]
  simp only [Iso.inv_hom_id_assoc]
  rw [MappedSingleCoordinates.comparison J M c g F W B E r s V T l t]
  rw [coefficient_eq J M c d g F W B E r s V T l t]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.MappedSingleDegreeCoordinates
