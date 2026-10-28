import OAI.AlgebraicGeometry.CycleClass.Thom.SegreCoordinates
import OAI.AlgebraicGeometry.CycleClass.Thom.ProjectiveCoordinates
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectivePointInjective

/-! # Segre Compatibility -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SegreCompatibility.Constructions.ProjectiveProducts

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- Evaluation commutes with the pairwise coordinate products. -/
theorem pointEvaluate_segreVector {X : Scheme} (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) {m n : ℕ}
    (v : Fin (m + 1) → Γ(X, ⊤)) (w : Fin (n + 1) → Γ(X, ⊤)) :
    (fun k => ProjectiveCoordinates.Constructions.Products.pointEvaluate p (SegreCoordinates.Constructions.ProjectiveProducts.segreVector v w k)) =
      SegreCoordinates.Constructions.ProjectiveProducts.segreVector (fun k => ProjectiveCoordinates.Constructions.Products.pointEvaluate p (v k)) (fun k => ProjectiveCoordinates.Constructions.Products.pointEvaluate p (w k)) := by
  funext k
  simp [SegreCoordinates.Constructions.ProjectiveProducts.segreVector]

/-- Equal normalized projective maps have proportional evaluated coordinate
tuples at each complex point. -/
theorem evaluated_coordinates_proportional {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) (hp : p ≫ f = 𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) {n : ℕ}
    (v v' : Fin (n + 1) → Γ(X, ⊤)) (i i' : Fin (n + 1)) (hv : v i = 1) (hv' : v' i' = 1)
    (heq : ProjectiveCoordinates.Constructions.Products.projectiveMapOfCoordinates f v i hv = ProjectiveCoordinates.Constructions.Products.projectiveMapOfCoordinates f v' i' hv') :
    ∃ c : ℂ, c ≠ 0 ∧
      (fun k => ProjectiveCoordinates.Constructions.Products.pointEvaluate p (v' k)) = c • (fun k => ProjectiveCoordinates.Constructions.Products.pointEvaluate p (v k)) := by
  have h := congrArg (fun q => p ≫ q) heq
  rw [ProjectiveCoordinates.Constructions.Products.projectiveMapOfCoordinates_point f p hp v i hv (ProjectiveCoordinates.Constructions.Products.pointEvaluate_tuple_ne_zero p v i hv),
    ProjectiveCoordinates.Constructions.Products.projectiveMapOfCoordinates_point f p hp v' i' hv' (ProjectiveCoordinates.Constructions.Products.pointEvaluate_tuple_ne_zero p v' i' hv')] at h
  exact Foundations.Scheme.ProjectivePointInjective.exists_smul_eq_of_projectiveVectorPoint_apply_eq _ _
    (ProjectiveCoordinates.Constructions.Products.pointEvaluate_tuple_ne_zero p v i hv) (ProjectiveCoordinates.Constructions.Products.pointEvaluate_tuple_ne_zero p v' i' hv')
    (IsLocalRing.closedPoint ℂ) (congrArg (fun q => q (IsLocalRing.closedPoint ℂ)) h)

/-- The local Segre morphism depends only on the two projective morphisms,
and is independent of the normalized coordinate tuples representing them. -/
theorem segreMapOfCoordinates_eq (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [LocallyOfFiniteType X.hom] [IsReduced X.left] {m n : ℕ}
    (v v' : Fin (m + 1) → Γ(X.left, ⊤)) (w w' : Fin (n + 1) → Γ(X.left, ⊤))
    (i i' : Fin (m + 1)) (j j' : Fin (n + 1))
    (hv : v i = 1) (hv' : v' i' = 1) (hw : w j = 1) (hw' : w' j' = 1)
    (hvmap : ProjectiveCoordinates.Constructions.Products.projectiveMapOfCoordinates X.hom v i hv = ProjectiveCoordinates.Constructions.Products.projectiveMapOfCoordinates X.hom v' i' hv')
    (hwmap : ProjectiveCoordinates.Constructions.Products.projectiveMapOfCoordinates X.hom w j hw = ProjectiveCoordinates.Constructions.Products.projectiveMapOfCoordinates X.hom w' j' hw') :
    SegreCoordinates.Constructions.ProjectiveProducts.segreMapOfCoordinates X.hom v w i j hv hw =
      SegreCoordinates.Constructions.ProjectiveProducts.segreMapOfCoordinates X.hom v' w' i' j' hv' hw' := by
  apply ProjectiveCoordinates.Constructions.Products.projectiveMapOfCoordinates_eq_of_point_scalars X
  intro p
  obtain ⟨c, hc, hvp⟩ := evaluated_coordinates_proportional X.hom p.left p.w v v' i i' hv hv' hvmap
  obtain ⟨d, hd, hwp⟩ := evaluated_coordinates_proportional X.hom p.left p.w w w' j j' hw hw' hwmap
  refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
  rw [pointEvaluate_segreVector, pointEvaluate_segreVector, hvp, hwp, SegreCoordinates.Constructions.ProjectiveProducts.segreVector_smul]

set_option backward.isDefEq.respectTransparency false in
/-- Local Segre maps commute with pullback of their coordinate functions. -/
theorem segreMapOfCoordinates_comp (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [LocallyOfFiniteType X.hom] [IsReduced X.left] (h : X ⟶ Y) {m n : ℕ}
    (v : Fin (m + 1) → Γ(Y.left, ⊤)) (w : Fin (n + 1) → Γ(Y.left, ⊤))
    (i : Fin (m + 1)) (j : Fin (n + 1)) (hv : v i = 1) (hw : w j = 1) :
    h.left ≫ SegreCoordinates.Constructions.ProjectiveProducts.segreMapOfCoordinates Y.hom v w i j hv hw =
      SegreCoordinates.Constructions.ProjectiveProducts.segreMapOfCoordinates X.hom (fun k => h.left.appTop (v k)) (fun k => h.left.appTop (w k))
        i j (by simp [hv]) (by simp [hw]) := by
  have hs : (fun k => h.left.appTop (SegreCoordinates.Constructions.ProjectiveProducts.segreVector v w k)) =
      SegreCoordinates.Constructions.ProjectiveProducts.segreVector (fun k => h.left.appTop (v k)) (fun k => h.left.appTop (w k)) := by
    funext k
    simp [SegreCoordinates.Constructions.ProjectiveProducts.segreVector]
  unfold SegreCoordinates.Constructions.ProjectiveProducts.segreMapOfCoordinates
  rw [ProjectiveCoordinates.Constructions.Products.projectiveMapOfCoordinates_comp X Y h]
  rw! [hs]
  rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SegreCompatibility.Constructions.ProjectiveProducts
