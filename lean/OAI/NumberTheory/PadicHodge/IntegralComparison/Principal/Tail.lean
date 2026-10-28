import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafCover

/-! # Tail -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.Tail.Comparison

noncomputable section

/-! The original relative and global refinement factors respect an
explicit equality of their ambient open. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X : TopCat.{u}} (U : Opens X)
  {ι κ ν μ ρ : Type u}
  [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] [LinearOrder μ] [LinearOrder ρ]
  (W : ι → Opens X) (B : κ → Opens X) (J : ν → Opens X)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι W)
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ B)
  (V : μ → Opens X) (T : ρ → Opens X)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover U B))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  (K : CochainComplex ((Opens X)ᵒᵖ ⥤ A) ℕ) (q : ℕ)
  [IsIso (RelativeCech.Refinement.homology U B J s K q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t K) q)]

def map := Relative.PresheafCommonRefinement.comparison U W B J r s K q ≫
  Presheaf.OrderedCover.Comparison.comparison
    (RelativeCech.Intersections.cover U B) V T l t K q

variable (U' : Opens X) (h : U = U')

def refinement : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover U' B) :=
  l ≫ eqToHom (congrArg (fun Q => FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover Q B)) h)

include h in
theorem relative_isIso : IsIso (RelativeCech.Refinement.homology U' B J s K q) := by
  subst U'
  infer_instance

def sourceTransport := HomologicalComplex₂.total.map
  (eqToHom (congrArg (fun Q => RelativeCech.Total.source Q W K) h)) (.up ℕ)

theorem transport :
    letI := relative_isIso U B J s K q U' h
    homologyMap (sourceTransport U W K U' h) q ≫
      Comparison.map U' W B J r s V T (refinement U B T l U' h) t K q =
    Comparison.map U W B J r s V T l t K q := by
  subst U'
  simp only [sourceTransport, refinement, eqToHom_refl, Category.comp_id,
    HomologicalComplex₂.total.map_id, homologyMap_id, Category.id_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.Tail.Comparison
