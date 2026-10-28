import OAI.AlgebraicGeometry.SheafCohomology.Cech.UpNatVerticalEdge

/-! # Bicomplex Coefficient Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexCoefficientEdge

noncomputable section

/-! Actual zeroth-row augmentations into a total complex are natural for
genuine bicomplex maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C : Type*} [Category C] [Preadditive C]
  (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) [K.HasTotal (.up ℕ)]
  (A : CochainComplex C ℕ) (u : A ⟶ K.X 0) (hu : u ≫ K.d 0 1 = 0)

def edge : A ⟶ K.total (.up ℕ) :=
  (AlgebraicGeometry.SheafCohomology.Cech.UpNatVerticalEdge.HomologicalComplex₂.totalUpNatVerticalEdge K) A (fun a => u.f a) (fun a a' _ => u.comm a a')
    (fun a => congrArg (fun f => f.f a) hu)

theorem component (a : ℕ) : (edge K A u hu).f a =
    u.f a ≫ K.ιTotal (.up ℕ) 0 a a (Nat.zero_add a) :=
  AlgebraicGeometry.SheafCohomology.Cech.UpNatVerticalEdge.HomologicalComplex₂.totalUpNatVerticalEdge_f _ _ _ _ _ a

variable {L : HomologicalComplex₂ C (.up ℕ) (.up ℕ)} [L.HasTotal (.up ℕ)]
  (B : CochainComplex C ℕ) (v : B ⟶ L.X 0) (hv : v ≫ L.d 0 1 = 0)
  (φ : K ⟶ L) (a : A ⟶ B) (h : u ≫ φ.f 0 = a ≫ v)

include h in
theorem naturality : edge K A u hu ≫ HomologicalComplex₂.total.map φ (.up ℕ) =
    a ≫ edge L B v hv := by
  apply HomologicalComplex.Hom.ext
  funext n
  have hn : u.f n ≫ (φ.f 0).f n = a.f n ≫ v.f n := congrArg (fun f => f.f n) h
  simp only [HomologicalComplex.comp_f, component, Category.assoc,
    HomologicalComplex₂.ιTotal_map]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ L.ιTotal (.up ℕ) 0 n n (Nat.zero_add n)) hn).trans
      (Category.assoc _ _ _))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexCoefficientEdge
