import OAI.NumberTheory.PadicHodge.IntegralComparison.TotalComponentLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.LowerHomotopy

/-! # Total Homotopy Assembly -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TotalHomotopyAssembly

noncomputable section

/-! Assemble a homotopy into the original first-quadrant total
complex from the degree-zero, edge, and interior component identities. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
  (K : CochainComplex C ℕ) (B : HomologicalComplex₂ C (.up ℕ) (.up ℕ))
  [B.HasTotal (.up ℕ)]

def signedComponent (h : ∀ p q, K.X (p + q + 1) ⟶ (B.X p).X q)
    (n p q : ℕ) (hpq : p + q = n) : K.X (n + 1) ⟶ (B.X p).X q :=
  (-1 : ℤ) ^ p • (eqToHom
    (congrArg K.X (congrArg (fun a => a + 1) hpq.symm)) ≫ h p q)

omit [B.HasTotal (.up ℕ)] in
theorem signedComponent_self (h : ∀ p q, K.X (p + q + 1) ⟶ (B.X p).X q)
    (p q : ℕ) : signedComponent K B h (p + q) p q rfl = (-1 : ℤ) ^ p • h p q := by
  simp only [signedComponent, eqToHom_refl, Category.id_comp]

variable (f g : K ⟶ B.total (.up ℕ))

structure Data where
  component : ∀ n p q, p + q = n → (K.X (n + 1) ⟶ (B.X p).X q)
  zero : (f.f 0 - g.f 0) ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 0 0 0 =
    K.d 0 1 ≫ component 0 0 0 rfl
  left : ∀ n, (f.f (n + 1) - g.f (n + 1)) ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 0 (n + 1) (n + 1) =
    K.d (n + 1) (n + 2) ≫ component (n + 1) 0 (n + 1) (by omega) +
      component n 0 n (by omega) ≫ (B.X 0).d n (n + 1)
  right : ∀ n, (f.f (n + 1) - g.f (n + 1)) ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) (n + 1) 0 (n + 1) =
    K.d (n + 1) (n + 2) ≫ component (n + 1) (n + 1) 0 (by omega) +
      component n n 0 (by omega) ≫ (B.d n (n + 1)).f 0
  interior : ∀ p q,
    (f.f (p + q + 2) - g.f (p + q + 2)) ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) (p + 1) (q + 1) (p + q + 2) =
      K.d (p + q + 2) (p + q + 3) ≫ component (p + q + 2) (p + 1) (q + 1) (by omega) +
        (component (p + q + 1) p (q + 1) (by omega) ≫ (B.d p (p + 1)).f (q + 1) +
          ((-1 : ℤˣ) ^ (p + 1)) •
            (component (p + q + 1) (p + 1) q (by omega) ≫ (B.X (p + 1)).d q (q + 1)))

variable (D : Data K B f g)

def component (n : ℕ) : K.X (n + 1) ⟶ (B.total (.up ℕ)).X n :=
  TotalComponentLift.lift B n (D.component n)

@[reassoc]
theorem component_projection (n p q : ℕ) (hpq : p + q = n) :
    TotalHomotopyAssembly.component K B f g D n ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) p q n = D.component n p q hpq :=
  TotalComponentLift.lift_projection B n (D.component n) p q hpq

theorem zero : f.f 0 - g.f 0 = K.d 0 1 ≫ TotalHomotopyAssembly.component K B f g D 0 := by
  apply AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatCoordinates.Projective.totalUpNat_hom_ext B 0
  intro i
  have hi : i = 0 := by apply Fin.ext; omega
  subst i
  change (f.f 0 - g.f 0) ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 0 0 0 =
    (K.d 0 1 ≫ TotalHomotopyAssembly.component K B f g D 0) ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) 0 0 0
  rw [Category.assoc, component_projection K B f g D 0 0 0 rfl]
  exact D.zero

theorem successor_projection (n p q : ℕ) (hpq : p + q = n + 1) :
    (f.f (n + 1) - g.f (n + 1)) ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) p q (n + 1) =
      (K.d (n + 1) (n + 2) ≫ TotalHomotopyAssembly.component K B f g D (n + 1) +
        TotalHomotopyAssembly.component K B f g D n ≫ (B.total (.up ℕ)).d n (n + 1)) ≫
          (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat B) p q (n + 1) := by
  rw [add_comp, Category.assoc, component_projection K B f g D (n + 1) p q hpq,
    Category.assoc]
  cases p with
  | zero =>
      have hq : q = n + 1 := by omega
      subst q
      rw [AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary.Projective.total_d_π_zero, ← Category.assoc,
        component_projection K B f g D n 0 n (by omega)]
      exact D.left n
  | succ p =>
      cases q with
      | zero =>
          have hp : p = n := by omega
          subst p
          rw [AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary.Projective.total_d_π_zero_right, ← Category.assoc,
            component_projection K B f g D n n 0 (by omega)]
          exact D.right n
      | succ q =>
          have hn : n = p + q + 1 := by omega
          subst n
          rw [AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary.Projective.total_d_π_interior, comp_add, Linear.comp_units_smul,
            ← Category.assoc, ← Category.assoc,
            component_projection K B f g D (p + q + 1) p (q + 1) (by omega),
            component_projection K B f g D (p + q + 1) (p + 1) q (by omega)]
          simpa only [Nat.add_assoc] using D.interior p q

theorem successor (n : ℕ) : f.f (n + 1) - g.f (n + 1) =
    K.d (n + 1) (n + 2) ≫ TotalHomotopyAssembly.component K B f g D (n + 1) +
      TotalHomotopyAssembly.component K B f g D n ≫ (B.total (.up ℕ)).d n (n + 1) := by
  apply AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatCoordinates.Projective.totalUpNat_hom_ext B (n + 1)
  intro i
  exact successor_projection K B f g D n i (n + 1 - i) (by omega)

def homotopy : Homotopy f g :=
  Cochain.LowerHomotopy.homotopy K (B.total (.up ℕ)) (TotalHomotopyAssembly.component K B f g D) f g
    (TotalHomotopyAssembly.zero K B f g D) (successor K B f g D)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TotalHomotopyAssembly
