import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafCover

/-! # Presheaf Functor Congruence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafFunctorCongruence

noncomputable section

/-! The literal principal comparison transports along equality of its
open-diagram functor, retaining the actual refinement arrows. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X : TopCat.{u}} {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {G : C ⥤ Opens X} (e : F = G)
  {ι κ ν μ ρ : Type u}
  [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] [LinearOrder μ] [LinearOrder ρ]
  (W : ι → C)
  [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) F]
  (B : κ → Opens X) (J : ν → Opens X)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (F.obj ∘ W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ B)
  (V : μ → Opens X) (T : ρ → Opens X)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) B))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  (K : CochainComplex ((Opens X)ᵒᵖ ⥤ A) ℕ) (q : ℕ)
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B J s K q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t K) q)]

def localRefinement : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (G.obj ∘ W) :=
  r ≫ eqToHom (congrArg (fun H : C ⥤ Opens X => FormalCoproduct.mk ι (H.obj ∘ W)) e)

def globalRefinement : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover (G.obj (⊤_ C)) B) :=
  l ≫ eqToHom (congrArg (fun H : C ⥤ Opens X => FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover (H.obj (⊤_ C)) B)) e)

def sourceIso := eqToIso (congrArg (fun H : C ⥤ Opens X =>
  (AugmentedOrdered.CechFunctor.bicomplex W
    (((AugmentedCech.AmbientTotal.restriction H).mapHomologicalComplex (.up ℕ)).obj K)).total (.up ℕ)) e)

include e in
omit [HasFiniteProducts C] [LinearOrder ι] in
theorem tuple_preserves : ∀ (n : ℕ) (a : Fin (n+1) → ι),
    PreservesLimit (Discrete.functor (W ∘ a)) G := by
  subst G
  infer_instance

include e in
theorem relative_isIso :
    IsIso (RelativeCech.Refinement.homology (G.obj (⊤_ C)) B J s K q) := by
  subst G
  infer_instance

theorem comparison :
    letI := tuple_preserves F e W
    letI := relative_isIso F e B J s K q
    homologyMap (sourceIso F e W K).hom q ≫
      PresheafCover.Comparison.comparison G W B J
        (localRefinement F e W J r) s V T (globalRefinement F e B T l) t K q =
    PresheafCover.Comparison.comparison F W B J r s V T l t K q := by
  subst G
  simp only [sourceIso, localRefinement, globalRefinement, eqToIso.hom, eqToHom_refl,
    homologyMap_id, Category.id_comp, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafFunctorCongruence
