import OAI.NumberTheory.PadicHodge.IntegralComparison.TotalComponentLift

/-! # Total Component Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TotalComponentMap

noncomputable section

/-! A map to a first-quadrant total from its signed differential
identities at the two edges and in the interior. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
  (L : CochainComplex C ℕ) (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ))
  [K.HasTotal (.up ℕ)]

structure Data where
  component : ∀ n p q, p + q = n → (L.X n ⟶ (K.X p).X q)
  left : ∀ n, component n 0 n (by omega) ≫ (K.X 0).d n (n + 1) =
    L.d n (n + 1) ≫ component (n + 1) 0 (n + 1) (by omega)
  right : ∀ n, component n n 0 (by omega) ≫ (K.d n (n + 1)).f 0 =
    L.d n (n + 1) ≫ component (n + 1) (n + 1) 0 (by omega)
  interior : ∀ p q,
    component (p + q + 1) p (q + 1) (by omega) ≫ (K.d p (p + 1)).f (q + 1) +
      ((-1 : ℤˣ) ^ (p + 1)) •
        (component (p + q + 1) (p + 1) q (by omega) ≫ (K.X (p + 1)).d q (q + 1)) =
    L.d (p + q + 1) (p + q + 1 + 1) ≫
      component (p + q + 1 + 1) (p + 1) (q + 1) (by omega)

variable (D : Data L K)

def component (n : ℕ) : L.X n ⟶ (K.total (.up ℕ)).X n :=
  TotalComponentLift.lift K n (D.component n)

@[reassoc]
theorem component_projection (n p q : ℕ) (h : p + q = n) :
    TotalComponentMap.component L K D n ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) p q n = D.component n p q h :=
  TotalComponentLift.lift_projection K n (D.component n) p q h

theorem differential_projection (n p q : ℕ) (hpq : p + q = n + 1) :
    (TotalComponentMap.component L K D n ≫ (K.total (.up ℕ)).d n (n + 1)) ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) p q (n + 1) =
      (L.d n (n + 1) ≫ TotalComponentMap.component L K D (n + 1)) ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) p q (n + 1) := by
  cases p with
  | zero =>
      have hq : q = n + 1 := by omega
      subst q
      rw [Category.assoc, AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary.Projective.total_d_π_zero, ← Category.assoc,
        component_projection, Category.assoc, component_projection]
      exact D.left n
  | succ p =>
      cases q with
      | zero =>
          have hp : p = n := by omega
          subst p
          rw [Category.assoc, AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary.Projective.total_d_π_zero_right, ← Category.assoc,
            component_projection, Category.assoc, component_projection]
          exact D.right n
      | succ q =>
          have hn : n = p + q + 1 := by omega
          subst n
          rw [Category.assoc, AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary.Projective.total_d_π_interior, comp_add,
            Linear.comp_units_smul, ← Category.assoc, ← Category.assoc,
            component_projection, component_projection, Category.assoc, component_projection]
          exact D.interior p q

theorem differential (n : ℕ) :
    TotalComponentMap.component L K D n ≫ (K.total (.up ℕ)).d n (n + 1) =
      L.d n (n + 1) ≫ TotalComponentMap.component L K D (n + 1) := by
  apply AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatCoordinates.Projective.totalUpNat_hom_ext K (n + 1)
  intro i
  exact differential_projection L K D n i (n + 1 - i) (by omega)

def map : L ⟶ K.total (.up ℕ) where
  f := TotalComponentMap.component L K D
  comm' n m h := by
    obtain rfl : m = n + 1 := h.symm
    exact differential L K D n

@[reassoc]
theorem map_projection (n p q : ℕ) (h : p + q = n) :
    (map L K D).f n ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) p q n = D.component n p q h :=
  component_projection L K D n p q h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TotalComponentMap
