import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeTotal

/-! # Inverse Cech -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.InverseCech.InverseCechEdgeCoordinates

/-! Transport of an original horizontal Cech edge only uses the
zero-column component of the inverse bicomplex comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B D : HomologicalComplex₂ A (.up ℕ) (.up ℕ)} [B.HasTotal (.up ℕ)] [D.HasTotal (.up ℕ)]
  {M : CochainComplex A ℕ} (g : M ⟶ B.total (.up ℕ)) (a : B ⟶ D)
  (q : ℕ) (c : M.X q ⟶ (B.X q).X 0)
  (h : g.f q = c ≫ B.ιTotal (.up ℕ) q 0 q rfl)

include h in
theorem component : (g ≫ HomologicalComplex₂.total.map a (.up ℕ)).f q =
    c ≫ (a.f q).f 0 ≫ D.ιTotal (.up ℕ) q 0 q rfl :=
  (congrArg (fun x => x ≫ (HomologicalComplex₂.total.map a (.up ℕ)).f q) h).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun x => c ≫ x) (HomologicalComplex₂.ιTotal_map B D a (.up ℕ) q 0 q rfl)))

end OAI.NumberTheory.PadicHodge.GeometricComparison.InverseCech.InverseCechEdgeCoordinates
